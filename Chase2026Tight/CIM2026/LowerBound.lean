/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Records
public import Chase2026Tight.CIM2026.Lemma4_1
public import Chase2026Tight.CIM2026.StopAtPulls
public import Chase2026Tight.Mathlib.InformationTheory.KullbackLeibler.Pinsker
public import Chase2026Tight.Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lower bounds on the number of rounds of good SBI algorithms

The general forms of Lemmas 4.2 and 5.1, on general arm and expert types, with `ln(1 + n/8)` in
place of the paper's `ln(n/10)`, valid for every `n ≥ 1`: a good SBI algorithm pulls every batch
`u` at least `ln(1 + n/8) / (8 ε²)` times in expectation under `S_0`
(`ofReal_le_lintegral_pullsBefore`), hence plays at least `k ln(1 + n/8) / (8 ε²)` rounds
(`ofReal_le_lintegral_stoppingTime`).

The proof of the first bound: let `M = ⌊ln(1 + n/8)/(4 ε²)⌋ + 1` and let `B = stopAtPulls σ u M A'`
be the algorithm that runs `A'`, stops when `A'` stops or at its `M`-th pull of batch `u`, and
outputs `true` iff it has pulled batch `u` fewer than `M` times and `A'` outputs batch `0`. By the
record representation (`klDiv_outputMeasure_le_klDiv_pi`) and Lemma 4.1, the divergence between
the laws of the output of `B` under the mixture of the `S_(u, v)` and under `S_0` is at most
`((1 + 4ε²)^M - 1)/n ≤ 1/4`, so by Pinsker's inequality the probabilities of `true` differ by at
most `0.4`. Since `A'` is good, `B` outputs `true` with probability at most `0.05` under every
`S_(u, v)`, hence at most `0.45` under `S_0`, and the event "batch `u` is pulled fewer than `M`
times" has probability at most `0.45 + 0.05` under `S_0`. Markov's inequality concludes.

## Main definitions

* `pullsBefore σ b X τ`: the number of rounds before `τ` in which an arm of batch `b` is pulled.

## Main statements

* `ofReal_le_lintegral_pullsBefore` (`lem:two_batch_general`),
  `ofReal_le_lintegral_stoppingTime` (`lem:many_batches_general`).
* `one_add_pow_floor_sub_one_div_le`: `((1 + 4ε²)^M - 1)/n ≤ 1/4` for the `M` above.
* `sum_pullsBefore_le`: the stopping time is at least the sum over the batches of the pulls.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits
open scoped ENNReal ENat

namespace Chase2026Tight

variable {k n : ℕ} {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n} {τ' : Expert k n → ι}

/-- The number of rounds before the (random) time `τ` in which an arm of batch `b` is pulled. -/
noncomputable def pullsBefore {Ω : Type*} (σ : α → Arm k) (b : Batch k) (X : ℕ → Ω → α)
    (τ : Ω → ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' t : ℕ, if (t : ℕ∞) < τ ω ∧ (σ (X t ω)).batch = b then 1 else 0

section PullsBefore

variable {Ω : Type*}

/-- The number of pulls of a batch before a random time is measurable. -/
lemma measurable_pullsBefore {_mΩ : MeasurableSpace Ω} (σ : α → Arm k) (b : Batch k)
    {X : ℕ → Ω → α} {τ : Ω → ℕ∞} (hX : ∀ t, Measurable (X t))
    (hτ : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < τ ω}) :
    Measurable (pullsBefore σ b X τ) := by
  refine Measurable.tsum fun t ↦ Measurable.ite ?_ measurable_const measurable_const
  exact (hτ t).inter
    ((measurable_of_countable (fun a ↦ (σ a).batch)).comp (hX t) (measurableSet_singleton b))

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The number of pulls of batch `b` in the first `m` rounds is at most the number of pulls of `b`
before `τ`, if `m ≤ τ`. -/
lemma pullCount_history_le_pullsBefore {𝓞 𝓨 : Type*} (σ : α → Arm k) (b : Batch k)
    {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {τ : Ω → ℕ∞} {ω : Ω} {m : ℕ}
    (hm : (m : ℕ∞) ≤ τ ω) :
    (pullCount σ b (history O X Y m ω) : ℝ≥0∞) ≤ pullsBefore σ b X τ ω := by
  rw [pullCount_history, Finset.card_filter, Nat.cast_sum]
  calc ∑ i : Fin m, (((if (σ (X i ω)).batch = b then 1 else 0 : ℕ)) : ℝ≥0∞)
      = ∑ t ∈ Finset.range m, (if (t : ℕ∞) < τ ω ∧ (σ (X t ω)).batch = b then 1 else 0) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun t ↦ ((if (σ (X t ω)).batch = b then 1 else 0 : ℕ) : ℝ≥0∞))]
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        have : (t : ℕ∞) < τ ω := lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.1 ht) hm
        simp [this]
    _ ≤ pullsBefore σ b X τ ω := ENNReal.sum_le_tsum _

/-- For an injective `f`, at most one term of `∑ u, 1{p ∧ c = f u}` is nonzero. -/
private lemma sum_ite_and_eq_le {β γ : Type*} [Fintype β] [DecidableEq γ] {f : β → γ}
    (hf : Function.Injective f) (p : Prop) [Decidable p] (c : γ) :
    ∑ u, (if p ∧ c = f u then (1 : ℝ≥0∞) else 0) ≤ if p then 1 else 0 := by
  by_cases hp : p
  · simp only [hp, true_and, ite_true]
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun u ↦ c = f u).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb ↦ by
        rw [Finset.mem_filter] at ha hb
        exact hf (ha.2.symm.trans hb.2)
    exact_mod_cast this
  · simp [hp]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The time `τ` is at least the sum over the batches `u ∈ [k]` of the pulls of batch `u` before
`τ`. -/
lemma sum_pullsBefore_le (σ : α → Arm k) (X : ℕ → Ω → α) (τ : Ω → ℕ∞) (ω : Ω) :
    ∑ u : Fin k, pullsBefore σ (some u : Batch k) X τ ω ≤ τ ω := by
  unfold pullsBefore
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, ← ENNReal.tsum_ite_natCast_lt]
  exact ENNReal.tsum_le_tsum fun t ↦ sum_ite_and_eq_le (f := fun u : Fin k ↦ (some u : Batch k))
    (Option.some_injective _) _ _

end PullsBefore

/-! ### Arithmetic -/

/-- With `M = ⌊ln(1 + n/8) / (4 ε²)⌋ + 1`, the bound of Lemma 4.1 for `M` rounds is at most `1/4`:
`((1 + 4 ε²)^M - 1) / n ≤ 1/4`. -/
lemma one_add_pow_floor_sub_one_div_le {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1) :
    ((1 + 4 * ε ^ 2) ^ (⌊Real.log (1 + n / 8) / (4 * ε ^ 2)⌋₊ + 1) - 1) / n ≤ 1 / 4 := by
  obtain ⟨hε0, hε1⟩ := hε
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (1 + n / 8) := Real.log_nonneg (by linarith)
  set L := Real.log (1 + n / 8) with hL_def
  set y := 4 * ε ^ 2 with hy_def
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 0.04 := by nlinarith
  set M := ⌊L / y⌋₊ + 1 with hM_def
  have hM : (M : ℝ) ≤ L / y + 1 := by
    simp only [hM_def, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg hL hy0.le)]
  have h1 : (1 + y) ^ M ≤ Real.exp (M * y) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp y]) M
  have h2 : M * y ≤ L + y := by
    calc M * y ≤ (L / y + 1) * y := mul_le_mul_of_nonneg_right hM hy0.le
      _ = L + y := by field_simp
  have h3 : Real.exp (L + y) = (1 + n / 8) * Real.exp y := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  have h4 : Real.exp y ≤ 1.05 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (x := y)
      (by rw [abs_of_pos hy0]; linarith))).2
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have h5 : (1 + n / 8) * Real.exp y ≤ (1 + n / 8) * 1.05 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  linarith [Real.exp_le_exp.2 h2]

/-- **Pulls of a batch by a good SBI algorithm** (`lem:two_batch_general`). Under `S_0`, a good SBI
algorithm pulls every batch `u` at least `ln(1 + n/8) / (8 ε²)` times in expectation before it
stops. -/
lemma ofReal_le_lintegral_pullsBefore (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1) (hn : 1 ≤ n) {A' : IdentAlg (ι → α) α ℝ (Batch k)}
    (hA' : IsGoodOn σ ρ τ τ' ε A') (u : Fin k) {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → ι → α} {X : ℕ → Ω → α}
    {Y : ℕ → Ω → α → ℝ} {out : Ω → Batch k}
    (h : A'.comapBanditFeedback.IsRun (strategyOn σ ρ τ τ' ε Expert.zero) O X Y out P) :
    ENNReal.ofReal (Real.log (1 + n / 8) / (8 * ε ^ 2)) ≤
      ∫⁻ ω, pullsBefore σ (some u : Batch k) X (A'.comapBanditFeedback.stoppingTime O X Y) ω
        ∂P := by
  obtain ⟨hε0, hε1⟩ := hε
  set L := Real.log (1 + n / 8) with hL_def
  set M := ⌊L / (4 * ε ^ 2)⌋₊ + 1 with hM_def
  set C := A'.comapBanditFeedback with hC_def
  set D := (stopAtPulls σ u M A').comapBanditFeedback with hD_def
  set N := pullsBefore σ (some u : Batch k) X (C.stoppingTime O X Y) with hN_def
  set S₀ := strategyOn σ ρ τ τ' ε Expert.zero with hS₀_def
  have hseq := h.isAlgEnvSeq
  have hNm : Measurable N := measurable_pullsBefore σ _ hseq.measurable_action
    (IdentAlg.measurableSet_lt_stoppingTime hseq.measurable_obs hseq.measurable_action
      hseq.measurable_feedback)
  -- goodness of `A'` under `S_0` and under `S_(u, v)`
  have hgood₀ : C.outputMeasure S₀ {Batch.zero}ᶜ ≤ ENNReal.ofReal 0.05 := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hA' Expert.zero)
  have hgood : ∀ v : Fin n,
      C.outputMeasure (strategyOn σ ρ τ τ' ε (Expert.mk u v)) {Batch.zero} ≤
        ENNReal.ofReal 0.05 := by
    intro v
    refine (measure_mono fun b hb ↦ ?_).trans ((ofReal_measureReal).symm.le.trans
      (ENNReal.ofReal_le_ofReal (hA' (Expert.mk u v))))
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    change (Batch.zero : Batch k) ≠ specialBatch (Expert.mk u v)
    exact fun h' ↦ by cases h'
  -- Step 1: `P(N < M) ≤ P_0(B outputs true) + 0.05`
  have hstep1 : P {ω | N ω < M} ≤ D.outputMeasure S₀ {true} + ENNReal.ofReal 0.05 := by
    refine (measure_mono ?_).trans
      ((measure_le_outputMeasure_stopAtPulls_add (σ := σ) (u := u) (M := M) hseq).trans
        (add_le_add le_rfl hgood₀))
    intro ω hω m hm
    have := (pullCount_history_le_pullsBefore σ (some u : Batch k) (O := O) (Y := Y) hm).trans_lt
      hω
    exact_mod_cast this
  -- Step 2: the mixture
  set mix := (n : ℝ≥0∞)⁻¹ • ∑ v : Fin n, D.outputMeasure (strategyOn σ ρ τ τ' ε (Expert.mk u v))
    with hmix_def
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hmix_prob : IsProbabilityMeasure mix := by
    constructor
    simp only [hmix_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n)
  have hmix_true : mix {true} ≤ ENNReal.ofReal 0.05 := by
    simp only [hmix_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      smul_eq_mul]
    calc (n : ℝ≥0∞)⁻¹ * ∑ v : Fin n, D.outputMeasure (strategyOn σ ρ τ τ' ε (Expert.mk u v)) {true}
        ≤ (n : ℝ≥0∞)⁻¹ * ∑ v : Fin n, ENNReal.ofReal 0.05 := by
          gcongr with v
          exact outputMeasure_stopAtPulls_le _ |>.trans (hgood v)
      _ = ENNReal.ofReal 0.05 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  have hKL : klDiv mix (D.outputMeasure S₀) ≤ ENNReal.ofReal (1 / 4) :=
    (klDiv_outputMeasure_le_klDiv_pi hσρ hττ' (stopAtPulls σ u M A') u M
      fun _ _ hh ↦ Or.inr hh).trans ((klDiv_mixture_pi_roundLaw_le hn ⟨hε0, hε1⟩
        (by omega)).trans (ENNReal.ofReal_le_ofReal
          (one_add_pow_floor_sub_one_div_le hn ⟨hε0, hε1⟩)))
  have hpin := (ofReal_two_mul_sq_measureReal_sub_le_klDiv (P := mix) (Q := D.outputMeasure S₀)
    (measurableSet_singleton true)).trans hKL
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hpin
  have hmix_real : mix.real {true} ≤ 0.05 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hmix_true
  have hD_real : (D.outputMeasure S₀).real {true} ≤ 0.45 := by nlinarith
  have hD : D.outputMeasure S₀ {true} ≤ ENNReal.ofReal 0.45 := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hD_real
  -- Step 3: `P(M ≤ N) ≥ 1/2`
  have hlt : P {ω | N ω < M} ≤ ENNReal.ofReal 0.5 := by
    refine hstep1.trans ((add_le_add hD le_rfl).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hge : ENNReal.ofReal 0.5 ≤ P {ω | (M : ℝ≥0∞) ≤ N ω} := by
    have hcompl : {ω | (M : ℝ≥0∞) ≤ N ω} = {ω | N ω < M}ᶜ := by
      ext ω
      simp
    rw [hcompl, prob_compl_eq_one_sub (measurableSet_lt hNm measurable_const)]
    calc ENNReal.ofReal 0.5 = 1 - ENNReal.ofReal 0.5 := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ 1 - P {ω | N ω < M} := tsub_le_tsub_left hlt 1
  -- Step 4: Markov's inequality
  have hM : L / (4 * ε ^ 2) < M := by
    rw [hM_def]
    push_cast
    exact Nat.lt_floor_add_one _
  calc ENNReal.ofReal (L / (8 * ε ^ 2)) ≤ (M : ℝ≥0∞) * ENNReal.ofReal 0.5 := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : L / (8 * ε ^ 2) = L / (4 * ε ^ 2) * 0.5 := by field_simp; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hM.le (by norm_num)
    _ ≤ (M : ℝ≥0∞) * P {ω | (M : ℝ≥0∞) ≤ N ω} := by gcongr
    _ ≤ ∫⁻ ω, N ω ∂P := mul_meas_ge_le_lintegral₀ hNm.aemeasurable _

/-- **Rounds of a good SBI algorithm** (`lem:many_batches_general`). Under `S_0`, a good SBI
algorithm plays at least `k ln(1 + n/8) / (8 ε²)` rounds in expectation. -/
lemma ofReal_le_lintegral_stoppingTime (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1) (hn : 1 ≤ n) {A' : IdentAlg (ι → α) α ℝ (Batch k)}
    (hA' : IsGoodOn σ ρ τ τ' ε A') {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → ι → α} {X : ℕ → Ω → α}
    {Y : ℕ → Ω → α → ℝ} {out : Ω → Batch k}
    (h : A'.comapBanditFeedback.IsRun (strategyOn σ ρ τ τ' ε Expert.zero) O X Y out P) :
    ENNReal.ofReal (k * Real.log (1 + n / 8) / (8 * ε ^ 2)) ≤
      ∫⁻ ω, (A'.comapBanditFeedback.stoppingTime O X Y ω : ℝ≥0∞) ∂P := by
  have hseq := h.isAlgEnvSeq
  calc ENNReal.ofReal (k * Real.log (1 + n / 8) / (8 * ε ^ 2))
      = ∑ _u : Fin k, ENNReal.ofReal (Real.log (1 + n / 8) / (8 * ε ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_div_assoc]
    _ ≤ ∑ u : Fin k, ∫⁻ ω, pullsBefore σ (some u : Batch k) X
          (A'.comapBanditFeedback.stoppingTime O X Y) ω ∂P :=
        Finset.sum_le_sum fun u _ ↦ ofReal_le_lintegral_pullsBefore hσρ hττ' hε hn hA' u h
    _ = ∫⁻ ω, ∑ u : Fin k, pullsBefore σ (some u : Batch k) X
          (A'.comapBanditFeedback.stoppingTime O X Y) ω ∂P :=
        (lintegral_finsetSum' _ fun u _ ↦
          (measurable_pullsBefore σ _ hseq.measurable_action
            (IdentAlg.measurableSet_lt_stoppingTime hseq.measurable_obs hseq.measurable_action
              hseq.measurable_feedback)).aemeasurable).symm
    _ ≤ ∫⁻ ω, (A'.comapBanditFeedback.stoppingTime O X Y ω : ℝ≥0∞) ∂P :=
        lintegral_mono fun ω ↦ sum_pullsBefore_le σ X _ ω

/-- `ln(n/10) ≤ ln(1 + n/8)`. -/
lemma log_div_ten_le_log_one_add_div_eight {n : ℕ} (hn : 10 ≤ n) :
    Real.log (n / 10) ≤ Real.log (1 + n / 8) := by
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_le_log (by positivity) (by linarith)

end Chase2026Tight
