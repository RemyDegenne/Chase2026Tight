/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.FinEmbedding
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Regret of a learner against the strategies of the pool and pulls of the special batch

Under the strategy `S_θ`, the *special expert* is `θ` (expert `0` for `S_0`) and the special batch
is the batch of `θ`. Given the advice of a round, the expected loss of an arm is `1/2` for the arms
of the batches other than the special batch, `1/2 - ε/2` for arm `0` and `1/2 ± ε` for the arms of
the special batch of `S_(u, v)` (`meanLoss`), against `1/2 - ε` (resp. `1/2 - ε/2` for `S_0`) for
the arm advised by the special expert. Hence every round in which the learner does not pull an arm
of the special batch costs at least `ε/2` in expected regret against the special expert, and the
pseudo-regret after `T` rounds is at least `ε/2` times the expected number of rounds `t < T` in
which the special batch is not pulled.

The statements are on the general arm and expert types of `Embedding.lean`.

## Main definitions

* `meanLoss ε θ e a`: the expected loss of the arm `a` under `S_θ` given the advice `e`.

## Main statements

* `meanLoss_sub_meanLoss_adviceOf_ge`: the per-arm regret against the special expert.
* `hasCondDistrib_feedback_strategyOn` (`lem:loss_law_cond`): the conditional law of the losses of
  a round given the advice and the arm.
* `mul_measureReal_batch_ne_le_integral` (`lem:per_round_regret`): the per-round regret.
* `mul_sub_integral_pullCount_le_expertPseudoRegret` (`lem:regret_ge_pulls`):
  `R_T ≥ (ε/2) E[T - N_{u⋆}(T)]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Finset
open scoped ENNReal

namespace Chase2026Tight

variable {k n : ℕ}

/-! ### Expected losses given the advice -/

/-- Under the uniform law on `Fin k → Bool`, the bit `u` is `b` with probability `1/2`. -/
private lemma uniform_real_eval_eq (u : Fin k) (b : Bool) :
    ((PMF.uniformOfFintype (Fin k → Bool)).toMeasure).real {c | c u = b} = 1 / 2 := by
  classical
  have h_card : #{c : Fin k → Bool | c u = b} = #{c : Fin k → Bool | c u = !b} := by
    refine Finset.card_nbij' (fun c ↦ Function.update c u (!c u))
      (fun c ↦ Function.update c u (!c u)) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
      simp [hc]
    · intro c hc
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
      simp [hc]
    · intro c _
      ext j
      by_cases hj : j = u
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · intro c _
      ext j
      by_cases hj : j = u
      · subst hj; simp
      · simp [Function.update_of_ne hj]
  have h_add := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin k → Bool))) (fun c ↦ c u = b)
  have h_neg : #{c : Fin k → Bool | ¬ c u = b} = #{c : Fin k → Bool | c u = !b} := by
    congr 1; ext c; cases h : c u <;> cases b <;> simp [h]
  rw [h_neg, ← h_card, card_univ] at h_add
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (MeasurableSet.of_discrete),
    Fintype.card_subtype]
  simp only [Set.mem_ofPred_eq]
  rw [← h_add, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, Nat.cast_add]
  have h_pos : (#{c : Fin k → Bool | c u = b} : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin k → Bool) := Fintype.card_pos
    rw [← h_add] at this
    exact_mod_cast (by omega : #{c : Fin k → Bool | c u = b} ≠ 0)
  field_simp
  ring

/-- The integral of a function on `Bool` against `bern p`, for `p ∈ [0, 1]`. -/
private lemma integral_bern {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂bern p = p * f true + (1 - p) * f false := by
  rw [bern, integral_bernoulliMeasure, Set.coe_projIcc, max_eq_right (le_min zero_le_one hp0),
    min_eq_right hp1, smul_eq_mul, smul_eq_mul]

/-- The integral against `lossRandomness` of a function of the loss bit of arm `0`. -/
private lemma integral_lossRandomness_fst (ε : ℝ) (f : Bool → ℝ) :
    ∫ r, f r.1 ∂lossRandomness k ε = ∫ b, f b ∂bern (1 / 2 - ε / 2) := by
  rw [lossRandomness, integral_fun_fst, probReal_univ, one_smul]

/-- The integral against `lossRandomness` of a function of the uniform bits of the batches. -/
private lemma integral_lossRandomness_snd_fst (ε : ℝ) (f : (Fin k → Bool) → ℝ) :
    ∫ r, f r.2.1 ∂lossRandomness k ε
      = ∫ c, f c ∂(PMF.uniformOfFintype (Fin k → Bool)).toMeasure := by
  rw [lossRandomness]
  refine (integral_fun_snd (fun q : (Fin k → Bool) × Bool ↦ f q.1)).trans ?_
  rw [probReal_univ, one_smul, integral_fun_fst, probReal_univ, one_smul]

/-- The integral against `lossRandomness` of a function of the bit of the special expert. -/
private lemma integral_lossRandomness_snd_snd (ε : ℝ) (f : Bool → ℝ) :
    ∫ r, f r.2.2 ∂lossRandomness k ε = ∫ b, f b ∂bern (1 / 2 - ε) := by
  rw [lossRandomness]
  refine (integral_fun_snd (fun q : (Fin k → Bool) × Bool ↦ f q.2)).trans ?_
  rw [probReal_univ, one_smul, integral_fun_snd, probReal_univ, one_smul]

/-- The expected loss of the arm `a` under the strategy `S_θ`, when the advice is `e`. -/
noncomputable def meanLoss (ε : ℝ) (θ : Expert k n) (e : Expert k n → Arm k) (a : Arm k) : ℝ :=
  ∫ ℓ, ℓ a ∂lossLaw ε θ e

/-- The expected loss of an arm as an integral against the randomness of the losses. -/
lemma meanLoss_eq_integral (ε : ℝ) (θ : Expert k n) (e : Expert k n → Arm k) (a : Arm k) :
    meanLoss ε θ e a = ∫ r, lossOf θ e r a ∂lossRandomness k ε := by
  rw [meanLoss, lossLaw, integral_map (f := fun ℓ : Arm k → ℝ ↦ ℓ a)
    (measurable_of_countable _).aemeasurable (measurable_pi_apply a).aestronglyMeasurable]

/-- The expected loss of arm `0` is `1/2 - ε/2`. -/
lemma meanLoss_zero {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (θ : Expert k n)
    (e : Expert k n → Arm k) :
    meanLoss ε θ e Arm.zero = 1 / 2 - ε / 2 := by
  rw [meanLoss_eq_integral]
  change ∫ r, (fun b : Bool ↦ if b then (1 : ℝ) else 0) r.1 ∂lossRandomness k ε = _
  rw [integral_lossRandomness_fst ε (fun b : Bool ↦ if b then (1 : ℝ) else 0),
    integral_bern (by linarith) (by linarith)]
  simp

/-- The expected loss of an arm of a batch which is not the special batch is `1/2`. -/
lemma meanLoss_ofBatch_of_ne {ε : ℝ} {θ : Expert k n} {u : Fin k}
    (hθ : specialBatch θ ≠ some u) (e : Expert k n → Arm k) (b : Bool) :
    meanLoss ε θ e (Arm.ofBatch u b) = 1 / 2 := by
  have h r : correctArm θ e r u = r.2.1 u := by
    rcases θ with _ | ⟨u', v⟩
    · rfl
    · have hu : u ≠ u' := fun h ↦ hθ (by rw [h]; rfl)
      change (if u = u' then _ else r.2.1 u) = r.2.1 u
      rw [ite_eq_right hu]
  rw [meanLoss_eq_integral]
  change ∫ r, (if b = correctArm θ e r u then (0 : ℝ) else 1) ∂lossRandomness k ε = _
  simp_rw [h]
  change ∫ r, (fun c : Fin k → Bool ↦ if b = c u then (0 : ℝ) else 1) r.2.1
    ∂lossRandomness k ε = _
  rw [integral_lossRandomness_snd_fst ε (fun c : Fin k → Bool ↦ if b = c u then (0 : ℝ) else 1)]
  have : (fun c : Fin k → Bool ↦ if b = c u then (0 : ℝ) else 1)
      = Set.indicator {c | c u = !b} 1 := by
    ext c
    cases h : c u <;> cases b <;> simp [Set.indicator, h]
  rw [this, integral_indicator_one MeasurableSet.of_discrete, uniform_real_eval_eq]

/-- The expected loss of an arm of the special batch `u` of `S_(u, v)`: `1/2 - ε` for the arm
advised by the expert `(u, v)`, `1/2 + ε` for the other one. -/
lemma meanLoss_mk_ofBatch {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : Fin k) (v : Fin n)
    (e : Expert k n → Arm k) (b : Bool) :
    meanLoss ε (Expert.mk u v) e (Arm.ofBatch u b)
      = if b = bitsOf e u v then 1 / 2 - ε else 1 / 2 + ε := by
  have h r : lossOf (Expert.mk u v) e r (Arm.ofBatch u b)
      = (fun f : Bool ↦ if b = xor (bitsOf e u v) f then (0 : ℝ) else 1) r.2.2 := by
    change (if b = (if u = u then xor (bitsOf e u v) r.2.2 else r.2.1 u) then _ else _) = _
    simp
  rw [meanLoss_eq_integral, integral_congr_ae (ae_of_all _ h),
    integral_lossRandomness_snd_snd ε
      (fun f : Bool ↦ if b = xor (bitsOf e u v) f then (0 : ℝ) else 1),
    integral_bern (by linarith) (by linarith)]
  cases b <;> cases bitsOf e u v <;> norm_num <;> ring

/-- **Per-arm regret.** Under `S_θ`, with advice `adviceOf β`, the expected loss of an arm exceeds
the expected loss of the arm advised by the special expert `θ` by at least `ε/2` if the arm is not
in the special batch, and by at least `0` otherwise. -/
lemma meanLoss_sub_meanLoss_adviceOf_ge {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (θ : Expert k n) (β : Bits k n) (a : Arm k) :
    (if a.batch = specialBatch θ then 0 else ε / 2)
      ≤ meanLoss ε θ (adviceOf β) a - meanLoss ε θ (adviceOf β) (adviceOf β θ) := by
  have hθ : θ = Expert.zero ∨ ∃ u v, θ = Expert.mk u v := by
    rcases θ with _ | ⟨u, v⟩
    exacts [Or.inl rfl, Or.inr ⟨u, v, rfl⟩]
  have ha : a = Arm.zero ∨ ∃ u b, a = Arm.ofBatch u b := by
    rcases a with _ | ⟨u, b⟩
    exacts [Or.inl rfl, Or.inr ⟨u, b, rfl⟩]
  rcases hθ with rfl | ⟨u, v, rfl⟩
  · have h0 : meanLoss ε Expert.zero (adviceOf β) (adviceOf β Expert.zero) = 1 / 2 - ε / 2 :=
      meanLoss_zero hε0 (by linarith) _ _
    rcases ha with rfl | ⟨u', b, rfl⟩
    · have hb : (Arm.zero : Arm k).batch = specialBatch (Expert.zero : Expert k n) := rfl
      rw [ite_eq_left hb]
      exact (sub_self _).ge
    · have hb : specialBatch (Expert.zero : Expert k n) ≠ some u' := by intro h; cases h
      have hb' : (Arm.ofBatch u' b).batch ≠ specialBatch (Expert.zero : Expert k n) := by
        intro h; cases h
      rw [h0, meanLoss_ofBatch_of_ne hb, ite_eq_right hb']
      linarith
  · have h0 : meanLoss ε (Expert.mk u v) (adviceOf β) (adviceOf β (Expert.mk u v)) = 1 / 2 - ε :=
      (meanLoss_mk_ofBatch hε0 hε1 u v (adviceOf β) (β u v)).trans (ite_eq_left rfl)
    rw [h0]
    rcases ha with rfl | ⟨u', b, rfl⟩
    · have hb : (Arm.zero : Arm k).batch ≠ specialBatch (Expert.mk u v) := by intro h; cases h
      rw [meanLoss_zero hε0 (by linarith), ite_eq_right hb]
      linarith
    · by_cases hu : u' = u
      · subst hu
        have hb : (Arm.ofBatch u' b).batch = specialBatch (Expert.mk u' v) := rfl
        rw [meanLoss_mk_ofBatch hε0 hε1, ite_eq_left hb]
        split_ifs <;> linarith
      · have hb : specialBatch (Expert.mk u v) ≠ some u' := by intro h; cases h; exact hu rfl
        have hb' : (Arm.ofBatch u' b).batch ≠ specialBatch (Expert.mk u v) := by
          intro h; cases h; exact hu rfl
        rw [meanLoss_ofBatch_of_ne hb, ite_eq_right hb']
        linarith

/-! ### Runs against the strategies of the pool -/

section Runs

variable {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] {σ : α → Arm k}
  {ρ : Arm k → α} {τ : ι → Expert k n} {τ' : Expert k n → ι} {ε : ℝ} {θ : Expert k n}

/-- The advice of `strategyOn` is the lift of the advice `adviceOf β` of some advice bits `β`. -/
lemma strategyOn_obsIn [Finite ι] (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) :
    (strategyOn σ ρ τ τ' ε θ).ObsIn (Set.range fun β : Bits k n ↦ liftAdvice ρ τ (adviceOf β)) := by
  have hS : MeasurableSet (Set.range fun β : Bits k n ↦ liftAdvice ρ τ (adviceOf β)) :=
    (Set.finite_range _).measurableSet
  intro m h
  cases m with
  | zero =>
    have h0 : (strategyOn σ ρ τ τ' ε θ).obs 0
        = Kernel.const _ ((initAdvice k n).map (liftAdvice ρ τ)) := rfl
    rw [h0, Kernel.const_apply, initAdvice,
      Measure.map_map (measurable_liftAdvice ρ τ) (measurable_of_countable _)]
    exact (ae_map_iff (measurable_of_countable _).aemeasurable hS).mpr
      (ae_of_all _ fun β ↦ ⟨β, rfl⟩)
  | succ m =>
    have h0 : (strategyOn σ ρ τ τ' ε θ).obs (m + 1) = ((adviceKernel k n).comap
        (fun h ↦ (σ (h (Fin.last m)).action, reduceAdvice σ τ' (h (Fin.last m)).obs))
        (by fun_prop)).map (liftAdvice ρ τ) := rfl
    rw [h0, Kernel.map_apply _ (measurable_liftAdvice ρ τ), Kernel.comap_apply]
    rw [show ∀ q, adviceKernel k n q = nextAdvice q.1 q.2 from fun _ ↦ rfl, nextAdvice,
      Measure.map_map (measurable_liftAdvice ρ τ) (measurable_of_countable _)]
    exact (ae_map_iff (measurable_of_countable _).aemeasurable hS).mpr
      (ae_of_all _ fun β ↦ ⟨_, rfl⟩)

/-- The law of the losses of a round under `strategyOn … θ`, given the advice and the arm of the
round: the law `lossLaw ε θ e` of the losses given the reduced advice `e`, read through `σ`. -/
noncomputable def lossKernelOn (σ : α → Arm k) (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) :
    Kernel ((ι → α) × α) (α → ℝ) :=
  ((lossKernel ε θ).comap (fun p ↦ reduceAdvice σ τ' p.1) (by fun_prop)).map (fun ℓ ↦ ℓ ∘ σ)

/-- `lossKernelOn` is a Markov kernel. -/
instance : IsMarkovKernel (lossKernelOn σ τ' ε θ) := by
  unfold lossKernelOn
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The law of the losses given the advice `p.1` and the arm `p.2`. -/
lemma lossKernelOn_apply (p : (ι → α) × α) :
    lossKernelOn σ τ' ε θ p = (lossLaw ε θ (reduceAdvice σ τ' p.1)).map (fun ℓ ↦ ℓ ∘ σ) := by
  rw [lossKernelOn, Kernel.map_apply _ (by fun_prop), Kernel.comap_apply]
  rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm (ι → α) α (α → ℝ)} {O : ℕ → Ω → ι → α} {X : ℕ → Ω → α}
  {Y : ℕ → Ω → α → ℝ}

/-- **Conditional law of the losses** (`lem:loss_law_cond`). In a run against `strategyOn … θ`,
the loss vector of round `t` has conditional law `lossLaw ε θ e_t`, read through `σ`, given the
advice and the arm of round `t`, where `e_t` is the reduced advice of the round. -/
lemma hasCondDistrib_feedback_strategyOn
    (h : IsAlgEnvSeq O X Y alg (strategyOn σ ρ τ τ' ε θ) P) (t : ℕ) :
    HasCondDistrib (Y t) (fun ω ↦ (O t ω, X t ω)) (lossKernelOn σ τ' ε θ) P :=
  h.hasCondDistrib_feedback_of_eq_comap (f := fun p ↦ (p.1.2, p.2)) (by fun_prop) (by
    have h0 : (strategyOn σ ρ τ τ' ε θ).feedback t = ((lossKernel ε θ).comap
        (fun p ↦ reduceAdvice σ τ' p.1.2) (by fun_prop)).map (fun ℓ ↦ ℓ ∘ σ) := rfl
    ext p : 1
    rw [h0, Kernel.comap_apply, lossKernelOn_apply, Kernel.map_apply _ (by fun_prop),
      Kernel.comap_apply]
    rfl)

/-- In a run against `strategyOn … θ`, the loss of an arm chosen measurably is integrable (it
is in `{0, 1}`). -/
lemma integrable_feedback_strategyOn [Finite α]
    (h : IsAlgEnvSeq O X Y alg (strategyOn σ ρ τ τ' ε θ) P) (t : ℕ) {Z : Ω → α}
    (hZ : Measurable Z) :
    Integrable (fun ω ↦ Y t ω (Z ω)) P := by
  have hB : MeasurableSet (Set.univ.pi fun _ : α ↦ ({0, 1} : Set ℝ)) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_singleton 1).insert 0
  refine Integrable.of_mem_Icc 0 1 ((h.measurable_feedback t).eval_prod hZ).aemeasurable ?_
  filter_upwards [h.ae_feedback_mem (strategyOn_feedbackIn σ ρ τ τ' ε θ) hB t] with ω hω
  rcases hω (Z ω) (Set.mem_univ _) with h0 | h1
  · rw [h0]; simp
  · rw [Set.mem_singleton_iff.mp h1]; simp

/-- The expected regret, against the special expert, of the arm `a` under `strategyOn … θ`, when
the reduced advice is `adviceOf β`. -/
lemma integral_feedbackKernel_strategyOn (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j)
    (β : Bits k n) (a : α) :
    ∫ y, (y a - y (liftAdvice ρ τ (adviceOf β) (τ' θ)))
        ∂lossKernelOn σ τ' ε θ (liftAdvice ρ τ (adviceOf β), a)
      = meanLoss ε θ (adviceOf β) (σ a) - meanLoss ε θ (adviceOf β) (adviceOf β θ) := by
  have h_int (b : Arm k) : Integrable (fun ℓ : Arm k → ℝ ↦ ℓ b) (lossLaw ε θ (adviceOf β)) :=
    (integrable_map_measure (measurable_pi_apply b).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr Integrable.of_finite
  have hσ : σ (liftAdvice ρ τ (adviceOf β) (τ' θ)) = adviceOf β θ := by
    simp [liftAdvice, hσρ, hττ']
  rw [lossKernelOn_apply, reduceAdvice_liftAdvice hσρ hττ',
    integral_map (by fun_prop : Measurable fun ℓ : Arm k → ℝ ↦ ℓ ∘ σ).aemeasurable (by fun_prop)]
  simp only [Function.comp_apply, hσ]
  rw [integral_sub (h_int _) (h_int _), meanLoss, meanLoss]

/-- **Per-round regret** (`lem:per_round_regret`). In a run against `strategyOn … θ`, the expected
regret of round `t` against the special expert `τ' θ` is at least `ε/2` times the probability that
the arm of round `t` is not in the special batch. -/
lemma mul_measureReal_batch_ne_le_integral [Finite α] [Finite ι] (hσρ : ∀ a, σ (ρ a) = a)
    (hττ' : ∀ j, τ (τ' j) = j) (h : IsAlgEnvSeq O X Y alg (strategyOn σ ρ τ τ' ε θ) P)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (t : ℕ) :
    ε / 2 * P.real {ω | (σ (X t ω)).batch ≠ specialBatch θ}
      ≤ ∫ ω, (Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) ∂P := by
  set κ := lossKernelOn σ τ' ε θ with hκ
  have hcd : HasCondDistrib (Y t) (fun ω ↦ (O t ω, X t ω)) κ P :=
    hasCondDistrib_feedback_strategyOn h t
  have hW : Measurable fun ω ↦ (O t ω, X t ω) :=
    (h.measurable_obs t).prodMk (h.measurable_action t)
  have hWY : Measurable fun ω ↦ ((O t ω, X t ω), Y t ω) := hW.prodMk (h.measurable_feedback t)
  set F : ((ι → α) × α) × (α → ℝ) → ℝ := fun z ↦ z.2 z.1.2 - z.2 (z.1.1 (τ' θ)) with hF_def
  have hF : Measurable F :=
    (measurable_snd.eval_prod (measurable_snd.comp measurable_fst)).sub
      (measurable_snd.eval_prod ((measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)))
  have hint : Integrable (fun ω ↦ Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) P :=
    (integrable_feedback_strategyOn h t (h.measurable_action t)).sub
      (integrable_feedback_strategyOn h t ((measurable_pi_apply _).comp (h.measurable_obs t)))
  have h_map : P.map (fun ω ↦ ((O t ω, X t ω), Y t ω)) = P.map (fun ω ↦ (O t ω, X t ω)) ⊗ₘ κ :=
    hcd.map_eq
  have hFint : Integrable F (P.map (fun ω ↦ (O t ω, X t ω)) ⊗ₘ κ) := by
    rw [← h_map]
    exact (integrable_map_measure hF.aestronglyMeasurable hWY.aemeasurable).mpr hint
  have h_eq : ∫ ω, (Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) ∂P
      = ∫ x, ∫ y, F (x, y) ∂κ x ∂(P.map fun ω ↦ (O t ω, X t ω)) := by
    rw [← Measure.integral_compProd hFint, ← h_map,
      integral_map hWY.aemeasurable hF.aestronglyMeasurable]
  have hs : MeasurableSet {x : (ι → α) × α | (σ x.2).batch ≠ specialBatch θ} :=
    (Set.to_countable _).measurableSet
  have h_lhs : ε / 2 * P.real {ω | (σ (X t ω)).batch ≠ specialBatch θ}
      = ∫ x, (if (σ x.2).batch = specialBatch θ then 0 else ε / 2)
          ∂(P.map fun ω ↦ (O t ω, X t ω)) := by
    have : (fun x : (ι → α) × α ↦ if (σ x.2).batch = specialBatch θ then (0 : ℝ) else ε / 2)
        = {x | (σ x.2).batch ≠ specialBatch θ}.indicator (fun _ ↦ ε / 2) := by
      ext x
      by_cases hx : (σ x.2).batch = specialBatch θ <;> simp [hx]
    rw [this, integral_indicator_const _ hs, map_measureReal_apply hW hs, smul_eq_mul, mul_comm]
    rfl
  have hS : MeasurableSet (Set.range fun β : Bits k n ↦ liftAdvice ρ τ (adviceOf β)) :=
    (Set.finite_range _).measurableSet
  have hO := h.ae_obs_mem (strategyOn_obsIn σ ρ τ τ' ε θ) hS t
  rw [h_lhs, h_eq]
  refine integral_mono_ae Integrable.of_finite Integrable.of_finite ?_
  rw [Filter.EventuallyLE, ae_map_iff hW.aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [hO] with ω hω
  obtain ⟨β, hβ⟩ := hω
  simp only at hβ
  simp only [hF_def, hκ]
  rw [← hβ, integral_feedbackKernel_strategyOn hσρ hττ']
  exact meanLoss_sub_meanLoss_adviceOf_ge hε0 hε1 θ β (σ (X t ω))

omit [IsProbabilityMeasure P] in
/-- The expected number of pulls of the batch `b` in the first `T` rounds is the sum of the
probabilities that the arm of round `t < T` is in batch `b`. -/
lemma integral_pullCount_history [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t)) (b : Batch k)
    (T : ℕ) :
    ∫ ω, (pullCount σ b (history O X Y T ω) : ℝ) ∂P
      = ∑ t ∈ range T, P.real {ω | (σ (X t ω)).batch = b} := by
  have hs (t : ℕ) : MeasurableSet {ω | (σ (X t ω)).batch = b} :=
    hX t (MeasurableSet.of_discrete (s := {a : α | (σ a).batch = b}))
  have h_eq (ω : Ω) : (pullCount σ b (history O X Y T ω) : ℝ)
      = ∑ i : Fin T, {ω | (σ (X i ω)).batch = b}.indicator 1 ω := by
    simp only [pullCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rfl
  simp_rw [h_eq]
  rw [integral_finsetSum (s := univ)
    (f := fun (i : Fin T) ω ↦ {ω | (σ (X i ω)).batch = b}.indicator (1 : Ω → ℝ) ω)
    fun i _ ↦ (integrable_const 1).indicator (hs i)]
  simp_rw [integral_indicator_one (hs _)]
  exact Fin.sum_univ_eq_sum_range (fun t ↦ P.real {ω | (σ (X t ω)).batch = b}) T

/-- **Regret and pulls of the special batch** (`lem:regret_ge_pulls`). In a run against
`strategyOn … θ`, the pseudo-regret after `T` rounds is at least `ε/2` times the expected number
of rounds `t < T` in which the arm pulled is not in the special batch:
`R_T ≥ (ε/2) E[T - N_{u⋆}(T)]`. -/
lemma mul_sub_integral_pullCount_le_expertPseudoRegret [Fintype α] [DecidableEq α] [Finite ι]
    (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j)
    (h : IsAlgEnvSeq O X Y alg (strategyOn σ ρ τ τ' ε θ) P)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (T : ℕ) :
    ε / 2 * (T - ∫ ω, (pullCount σ (specialBatch θ) (history O X Y T ω) : ℝ) ∂P)
      ≤ expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) X Y T := by
  have hs (t : ℕ) : MeasurableSet {ω | (σ (X t ω)).batch = specialBatch θ} :=
    h.measurable_action t (MeasurableSet.of_discrete (s := {a : α | (σ a).batch = specialBatch θ}))
  have hint (t : ℕ) : Integrable (fun ω ↦ Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) P :=
    (integrable_feedback_strategyOn h t (h.measurable_action t)).sub
      (integrable_feedback_strategyOn h t ((measurable_pi_apply _).comp (h.measurable_obs t)))
  rw [integral_pullCount_history h.measurable_action, expertPseudoRegret_diracAdvice]
  calc ε / 2 * (T - ∑ t ∈ range T, P.real {ω | (σ (X t ω)).batch = specialBatch θ})
  _ = ∑ t ∈ range T, ε / 2 * P.real {ω | (σ (X t ω)).batch ≠ specialBatch θ} := by
    rw [← mul_sum]
    congr 1
    have h_compl (t : ℕ) : P.real {ω | (σ (X t ω)).batch ≠ specialBatch θ}
        = 1 - P.real {ω | (σ (X t ω)).batch = specialBatch θ} := by
      rw [← probReal_compl_eq_one_sub (hs t)]
      rfl
    simp_rw [h_compl, sum_sub_distrib]
    simp
  _ ≤ ∑ t ∈ range T, ∫ ω, (Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) ∂P :=
    sum_le_sum fun t _ ↦ mul_measureReal_batch_ne_le_integral hσρ hττ' h hε0 hε1 t
  _ = ∫ ω, ∑ t ∈ range T, (Y t ω (X t ω) - Y t ω (O t ω (τ' θ))) ∂P :=
    (integral_finsetSum _ fun t _ ↦ hint t).symm
  _ ≤ ⨆ j, ∫ ω, ∑ t ∈ range T, (Y t ω (X t ω) - Y t ω (O t ω j)) ∂P :=
    le_ciSup (f := fun j ↦ ∫ ω, ∑ t ∈ range T, (Y t ω (X t ω) - Y t ω (O t ω j)) ∂P)
      (Set.finite_range _).bddAbove (τ' θ)

end Runs

end Chase2026Tight
