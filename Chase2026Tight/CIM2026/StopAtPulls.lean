/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Embedding
public import Chase2026Tight.LeanMachineLearning.Online.Bandit.Adversarial
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.IdentificationAlg
public import Chase2026Tight.Mathlib.Probability.Process.HittingTime

/-!
# Stopping an SBI algorithm at its `M`-th pull of a batch

From an SBI algorithm `A` (with outputs in `Batch k`), a batch `u` and `M ∈ ℕ`, we build the
identification algorithm `stopAtPulls σ u M A` with Boolean output used in the proof of Lemma 4.2:
it runs the sampling rule of `A`, stops when `A` stops or as soon as it has pulled batch `u` `M`
times, and outputs `true` iff it has pulled batch `u` fewer than `M` times and the output of `A`
on the history (drawn from the output rule of `A`) is batch `0`.

Its output is `true` with probability at most the probability that `A` outputs batch `0`
(`outputMeasure_stopAtPulls_le`). Conversely, along a run of `A`, the event "batch `u` is pulled
fewer than `M` times up to the stopping time of `A`" has probability at most the probability that
`stopAtPulls σ u M A` outputs `true` plus the probability that `A` does not output batch `0`
(`measure_le_outputMeasure_stopAtPulls_add`): on that event both algorithms stop at the same time.

## Main definitions

* `stopAtPulls σ u M A`: the algorithm described above (`def:stop_at_pulls`).

## Main statements

* `outputMeasure_stopAtPulls_le`, `measure_le_outputMeasure_stopAtPulls_add`
  (`lem:stop_at_pulls_output`).
* `stoppingTime_comapBanditFeedback_stopAtPulls_eq`: if batch `u` is pulled fewer than `M` times
  up to the stopping time of `A`, both algorithms stop at the same time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Finset
open scoped ENNReal ENat

namespace Chase2026Tight

variable {k : ℕ} {α 𝓞 𝓨 : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  [MeasurableSpace 𝓞] [MeasurableSpace 𝓨]

/-! ### Pull counts -/

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] [MeasurableSpace 𝓞]
  [MeasurableSpace 𝓨] in
/-- The number of pulls of a batch only depends on the arms of the history, not on the
feedbacks. -/
lemma pullCount_partialFeedback {𝓦 : Type*} (σ : α → Arm k) (b : Batch k)
    (g : Round 𝓞 α 𝓨 → 𝓦) {m : ℕ} (h : Hist 𝓞 α 𝓨 m) :
    pullCount σ b (Hist.partialFeedback g h) = pullCount σ b h := rfl

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] [MeasurableSpace 𝓞]
  [MeasurableSpace 𝓨] in
/-- The number of pulls of batch `b` in the first `m` rounds of a sequence of arms `X`. -/
lemma pullCount_history {Ω : Type*} (σ : α → Arm k) (b : Batch k) (O : ℕ → Ω → 𝓞)
    (X : ℕ → Ω → α) (Y : ℕ → Ω → 𝓨) (m : ℕ) (ω : Ω) :
    pullCount σ b (history O X Y m ω) = #{i : Fin m | (σ (X i ω)).batch = b} := rfl

/-- The number of pulls of a batch in a history is a measurable function of the history. -/
lemma measurable_pullCount (σ : α → Arm k) (b : Batch k) (m : ℕ) :
    Measurable (fun h : Hist 𝓞 α 𝓨 m ↦ pullCount σ b h) := by
  have : (fun h : Hist 𝓞 α 𝓨 m ↦ pullCount σ b h) =
      (fun a : Fin m → α ↦ #{i | (σ (a i)).batch = b}) ∘ (fun h i ↦ (h i).action) := rfl
  rw [this]
  exact (measurable_of_countable _).comp
    (measurable_pi_iff.mpr fun i ↦ Round.measurable_action.comp (measurable_pi_apply i))

/-- The number of pulls of a batch in a history of variable length is measurable. -/
lemma measurable_sigma_pullCount (σ : α → Arm k) (b : Batch k) :
    Measurable (fun h : Σ m, Hist 𝓞 α 𝓨 m ↦ pullCount σ b h.2) :=
  measurable_sigma_of_measurable_comp_mk fun m ↦ measurable_pullCount σ b m

/-- The histories of variable length with fewer than `M` pulls of batch `b` form a measurable
set. -/
lemma measurableSet_pullCount_lt (σ : α → Arm k) (b : Batch k) (M : ℕ) :
    MeasurableSet {h : Σ m, Hist 𝓞 α 𝓨 m | pullCount σ b h.2 < M} :=
  measurable_sigma_pullCount σ b measurableSet_Iio

/-- The histories of variable length with at least `M` pulls of batch `b` form a measurable
set. -/
lemma measurableSet_le_pullCount (σ : α → Arm k) (b : Batch k) (M : ℕ) :
    MeasurableSet {h : Σ m, Hist 𝓞 α 𝓨 m | M ≤ pullCount σ b h.2} :=
  measurable_sigma_pullCount σ b measurableSet_Ici

/-! ### The algorithm -/

/-- The identification algorithm that runs the sampling rule of `A`, stops when `A` stops or as
soon as it has pulled batch `u` `M` times, and outputs `true` iff it has pulled batch `u` fewer
than `M` times and the output of `A` on the history is batch `0`. -/
noncomputable def stopAtPulls (σ : α → Arm k) (u : Fin k) (M : ℕ)
    (A : IdentAlg 𝓞 α 𝓨 (Batch k)) : IdentAlg 𝓞 α 𝓨 Bool where
  alg := A.alg
  stopSet := A.stopSet ∪ {h | M ≤ pullCount σ (some u : Batch k) h.2}
  measurableSet_stopSet :=
    A.measurableSet_stopSet.union (measurableSet_le_pullCount σ _ M)
  output := Kernel.piecewise (measurableSet_pullCount_lt σ (some u : Batch k) M)
    (A.output.map fun b ↦ decide (b = Batch.zero)) (Kernel.const _ (Measure.dirac false))
  isMarkovKernel_output :=
    have := Kernel.IsMarkovKernel.map A.output
      (measurable_of_countable fun b : Batch k ↦ decide (b = Batch.zero))
    Kernel.IsMarkovKernel.piecewise

variable {σ : α → Arm k} {u : Fin k} {M : ℕ} {A : IdentAlg 𝓞 α 𝓨 (Batch k)}

/-- `stopAtPulls σ u M A` has the sampling rule of `A`. -/
lemma stopAtPulls_alg : (stopAtPulls σ u M A).alg = A.alg := rfl

/-- With bandit feedback, the stopping rule of `stopAtPulls σ u M A` is that of `A` or `M` pulls of
batch `u`. -/
lemma stopSet_comapBanditFeedback_stopAtPulls :
    (stopAtPulls σ u M A).comapBanditFeedback.stopSet =
      A.comapBanditFeedback.stopSet ∪ {h | M ≤ pullCount σ (some u : Batch k) h.2} := rfl

/-- The probability that `stopAtPulls σ u M A` outputs `true` given a history: the probability that
`A` outputs batch `0` if batch `u` is pulled fewer than `M` times in the history, `0` otherwise. -/
lemma output_comapBanditFeedback_stopAtPulls_true (h : Σ m, Hist 𝓞 α (α → 𝓨) m) :
    (stopAtPulls σ u M A).comapBanditFeedback.output h {true} =
      if pullCount σ (some u : Batch k) h.2 < M then
        A.comapBanditFeedback.output h {Batch.zero} else 0 := by
  obtain ⟨m, h⟩ := h
  rw [IdentAlg.comapBanditFeedback, IdentAlg.comapBanditFeedback,
    IdentAlg.comapPartialFeedback_output_mk, IdentAlg.comapPartialFeedback_output_mk]
  by_cases hlt : pullCount σ (some u : Batch k) h < M
  · rw [ite_eq_left hlt]
    have hmem : (⟨m, Hist.partialFeedback banditFeedback h⟩ : Σ m, Hist 𝓞 α 𝓨 m) ∈
        {h : Σ m, Hist 𝓞 α 𝓨 m | pullCount σ (some u : Batch k) h.2 < M} := hlt
    simp only [stopAtPulls]
    rw [Kernel.piecewise_apply, ite_eq_left hmem,
      Kernel.map_apply' _ (measurable_of_countable _) _ (measurableSet_singleton true)]
    congr 1
    ext b
    simp
  · rw [ite_eq_right hlt]
    have hmem : (⟨m, Hist.partialFeedback banditFeedback h⟩ : Σ m, Hist 𝓞 α 𝓨 m) ∉
        {h : Σ m, Hist 𝓞 α 𝓨 m | pullCount σ (some u : Batch k) h.2 < M} := hlt
    simp only [stopAtPulls]
    rw [Kernel.piecewise_apply, ite_eq_right hmem]
    simp

/-! ### Stopping times and stopped histories -/

section Run

variable {Ω : Type*} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α} {Y : ℕ → Ω → α → 𝓨} {ω : Ω}

/-- `stopAtPulls σ u M A` stops at the latest when `A` stops. -/
lemma stoppingTime_comapBanditFeedback_stopAtPulls_le :
    (stopAtPulls σ u M A).comapBanditFeedback.stoppingTime O X Y ω ≤
      A.comapBanditFeedback.stoppingTime O X Y ω := by
  rw [IdentAlg.stoppingTime_def, IdentAlg.stoppingTime_def,
    stopSet_comapBanditFeedback_stopAtPulls]
  exact hittingAfter_anti _ 0 Set.subset_union_left ω

/-- If batch `u` is pulled fewer than `M` times up to the stopping time of `A`, then
`stopAtPulls σ u M A` stops at the same time as `A`. -/
lemma stoppingTime_comapBanditFeedback_stopAtPulls_eq
    (hω : ∀ m : ℕ, (m : ℕ∞) ≤ A.comapBanditFeedback.stoppingTime O X Y ω →
      pullCount σ (some u : Batch k) (history O X Y m ω) < M) :
    (stopAtPulls σ u M A).comapBanditFeedback.stoppingTime O X Y ω =
      A.comapBanditFeedback.stoppingTime O X Y ω := by
  rw [IdentAlg.stoppingTime_def, IdentAlg.stoppingTime_def,
    stopSet_comapBanditFeedback_stopAtPulls]
  exact hittingAfter_union_of_forall_notMem fun m _ hm ↦ not_le.2 (hω m hm)

/-- If batch `u` is pulled fewer than `M` times in the history at the stopping time of
`stopAtPulls σ u M A`, then this is the history at the stopping time of `A`. -/
lemma stoppedHist_comapBanditFeedback_stopAtPulls_eq
    (hω : pullCount σ (some u : Batch k)
      ((stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω).2 < M) :
    (stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω =
      A.comapBanditFeedback.stoppedHist O X Y ω := by
  suffices h : (stopAtPulls σ u M A).comapBanditFeedback.stoppingTime O X Y ω =
      A.comapBanditFeedback.stoppingTime O X Y ω by
    simp only [IdentAlg.stoppedHist_def, stoppedValue, h]
  refine le_antisymm stoppingTime_comapBanditFeedback_stopAtPulls_le ?_
  cases hτ : (stopAtPulls σ u M A).comapBanditFeedback.stoppingTime O X Y ω with
  | top => exact le_top
  | coe i =>
    have hmem := IdentAlg.stoppedHist_mem_stopSet_of_ne_top
      (A := (stopAtPulls σ u M A).comapBanditFeedback) (O := O) (X := X) (Y := Y) (ω := ω)
      (by simp [hτ])
    have hi : (stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω =
        sigmaHistory O X Y i ω := by
      simp [IdentAlg.stoppedHist_def, stoppedValue, hτ, WithTop.untopA]
    rw [stopSet_comapBanditFeedback_stopAtPulls] at hmem
    rcases hmem with hmem | hmem
    · rw [hi] at hmem
      exact hittingAfter_le_of_mem (Nat.zero_le _) hmem
    · exact absurd hmem (not_le.2 hω)

/-- Along any run, the probability that `stopAtPulls σ u M A` outputs `true` given its stopped
history is at most the probability that `A` outputs batch `0` given its stopped history. -/
lemma output_stoppedHist_stopAtPulls_le :
    (stopAtPulls σ u M A).comapBanditFeedback.output
        ((stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω) {true} ≤
      A.comapBanditFeedback.output (A.comapBanditFeedback.stoppedHist O X Y ω) {Batch.zero} := by
  rw [output_comapBanditFeedback_stopAtPulls_true]
  split_ifs with hlt
  · rw [stoppedHist_comapBanditFeedback_stopAtPulls_eq hlt]
  · exact zero_le

/-- If batch `u` is pulled fewer than `M` times up to the stopping time of `A`, then the
probability that `stopAtPulls σ u M A` outputs `true` given its stopped history plus the
probability that `A` does not output batch `0` given its stopped history is `1`. -/
lemma one_le_output_stoppedHist_stopAtPulls_add
    (hω : ∀ m : ℕ, (m : ℕ∞) ≤ A.comapBanditFeedback.stoppingTime O X Y ω →
      pullCount σ (some u : Batch k) (history O X Y m ω) < M) :
    1 ≤ (stopAtPulls σ u M A).comapBanditFeedback.output
        ((stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω) {true} +
      A.comapBanditFeedback.output (A.comapBanditFeedback.stoppedHist O X Y ω) {Batch.zero}ᶜ := by
  have hst : (stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω =
      A.comapBanditFeedback.stoppedHist O X Y ω := by
    simp only [IdentAlg.stoppedHist_def, stoppedValue,
      stoppingTime_comapBanditFeedback_stopAtPulls_eq hω]
  have hlt : pullCount σ (some u : Batch k) (A.comapBanditFeedback.stoppedHist O X Y ω).2 < M :=
    hω _ (WithTop.coe_untopA_le _)
  rw [hst, output_comapBanditFeedback_stopAtPulls_true, ite_eq_left hlt,
    measure_add_measure_compl (measurableSet_singleton _), measure_univ]

end Run

/-! ### Output laws -/

/-- `stopAtPulls σ u M A` outputs `true` with probability at most the probability that `A` outputs
batch `0`. -/
lemma outputMeasure_stopAtPulls_le (env : Environment 𝓞 α (α → 𝓨)) :
    (stopAtPulls σ u M A).comapBanditFeedback.outputMeasure env {true} ≤
      A.comapBanditFeedback.outputMeasure env {Batch.zero} := by
  have h := IT.isAlgEnvSeq_trajMeasure A.comapBanditFeedback.alg env
  rw [IdentAlg.outputMeasure_apply_eq_lintegral (A := (stopAtPulls σ u M A).comapBanditFeedback) h
      (measurableSet_singleton _),
    IdentAlg.outputMeasure_apply_eq_lintegral h (measurableSet_singleton _)]
  exact lintegral_mono fun ω ↦ output_stoppedHist_stopAtPulls_le

/-- Along a run of `A`, the probability that batch `u` is pulled fewer than `M` times up to the
stopping time of `A` is at most the probability that `stopAtPulls σ u M A` outputs `true` plus the
probability that `A` does not output batch `0`. -/
lemma measure_le_outputMeasure_stopAtPulls_add {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {env : Environment 𝓞 α (α → 𝓨)}
    {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α} {Y : ℕ → Ω → α → 𝓨}
    (h : IsAlgEnvSeq O X Y A.comapBanditFeedback.alg env P) :
    P {ω | ∀ m : ℕ, (m : ℕ∞) ≤ A.comapBanditFeedback.stoppingTime O X Y ω →
        pullCount σ (some u : Batch k) (history O X Y m ω) < M} ≤
      (stopAtPulls σ u M A).comapBanditFeedback.outputMeasure env {true} +
        A.comapBanditFeedback.outputMeasure env {Batch.zero}ᶜ := by
  have hD : Measurable fun ω ↦ (stopAtPulls σ u M A).comapBanditFeedback.output
      ((stopAtPulls σ u M A).comapBanditFeedback.stoppedHist O X Y ω) {true} :=
    (Kernel.measurable_coe _ (measurableSet_singleton _)).comp (IdentAlg.measurable_stoppedHist h)
  have hC : Measurable fun ω ↦ A.comapBanditFeedback.output
      (A.comapBanditFeedback.stoppedHist O X Y ω) {Batch.zero}ᶜ :=
    (Kernel.measurable_coe _ (measurableSet_singleton _).compl).comp
      (IdentAlg.measurable_stoppedHist h)
  rw [IdentAlg.outputMeasure_apply_eq_lintegral (A := (stopAtPulls σ u M A).comapBanditFeedback) h
      (measurableSet_singleton _),
    IdentAlg.outputMeasure_apply_eq_lintegral h (measurableSet_singleton _).compl,
    ← lintegral_add_left hD]
  have h_le := mul_meas_ge_le_lintegral₀ ((hD.add hC).aemeasurable (μ := P)) 1
  rw [one_mul] at h_le
  exact (measure_mono fun ω hω ↦ one_le_output_stoppedHist_stopAtPulls_add hω).trans h_le

end Chase2026Tight
