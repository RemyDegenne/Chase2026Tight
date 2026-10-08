/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Embedding
public import Chase2026Tight.CIM2026.RecordTape
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Representation of the runs by pull records

The advice of a batch is redrawn only after a pull of that batch, so the information that an
algorithm gathers on batch `u` comes as an i.i.d. sequence of *pull records* (the advice of the
batch and its correct arm at each pull), whatever the algorithm does between the pulls. Under the
strategies `S_0` and `S_(u, v)`, all the other variables of a run have the same law. Hence the law
of the output of an identification algorithm that stops at the latest at its `M`-th pull of batch
`u` is the image of `M` records and of variables whose law does not depend on the strategy, and the
data processing inequality bounds the divergence between the output laws under the uniform mixture
of the `S_(u, v)` and under `S_0` by the divergence of Lemma 4.1.

The representation is proved in `Chase2026Tight/CIM2026/RecordTape.lean` in the finite reduced
setting of `Chase2026Tight/CIM2026/ReducedRun.lean`: the output law under `S_0` or `S_(u, v)` is
`K ∘ₘ P^M` for a Markov kernel `K` not depending on the strategy, where `P` is the law of a round
of the two-batch game (`outputMeasure_eq_comp_pi_roundLaw`).

## Main statements

* `outputMeasure_eq_comp_pi_roundLaw`: the representation of the output laws.
* `klDiv_outputMeasure_le_klDiv_pi`: the data processing bound through the pull records.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

variable {k n : ℕ} {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n}
  {τ' : Expert k n → ι}

variable (σ ρ τ) in
/-- The kernel giving the law of the output of the identification algorithm `B` (with bandit
feedback, on the general types) as a function of the first `M` rounds of the two-batch game read as
the records of the first `M` pulls of batch `u`. -/
noncomputable def recordOutputKernel {𝓓 : Type*} [MeasurableSpace 𝓓] (ε : ℝ)
    (B : IdentAlg (ι → α) α ℝ 𝓓) (u : Fin k) (M : ℕ) : Kernel (Fin M → AdvLoss 1 n) 𝓓 :=
  ((reducedAlg ρ τ B).output ∘ₖ
    stoppedHistKernel (reducedAlg ρ τ B).alg (tapeStrategy σ ε u (M := M))
      (reducedAlg ρ τ B).stopSet).comap (fun s j ↦ recordOf (s j))
    (Measurable.of_eval fun j ↦ measurable_recordOf.comp (measurable_pi_apply j))

instance {𝓓 : Type*} [MeasurableSpace 𝓓] (ε : ℝ) (B : IdentAlg (ι → α) α ℝ 𝓓) (u : Fin k)
    (M : ℕ) : IsMarkovKernel (recordOutputKernel σ ρ τ ε B u M) := by
  unfold recordOutputKernel
  infer_instance

/-- **Representation of the output laws** (`lem:events_before_pulls`). Let `B` be an
identification algorithm (with bandit feedback) on the general types that stops at the latest
when it has pulled batch `u` `M` times. Under the strategy `S_0` (`w = none`) or `S_(u, v)`
(`w = some v`), the law of its output is the image of the law of `M` independent rounds of the
two-batch game under `S_0`, respectively `S_(1, v)`, by a Markov kernel that does not depend on the
strategy. -/
lemma outputMeasure_eq_comp_pi_roundLaw {𝓓 : Type*} [MeasurableSpace 𝓓]
    (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j) (ε : ℝ)
    (B : IdentAlg (ι → α) α ℝ 𝓓) (u : Fin k) (M : ℕ)
    (hB : ∀ m (h : Hist (ι → α) α ℝ m), M ≤ pullCount σ (some u : Batch k) h →
      (⟨m, h⟩ : Σ m, Hist (ι → α) α ℝ m) ∈ B.stopSet) (w : Option (Fin n)) :
    B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε (batchExpert u w)) =
      recordOutputKernel σ ρ τ ε B u M ∘ₘ
        Measure.pi fun _ : Fin M ↦ roundLaw (k := 1) ε (batchExpert 0 w) := by
  have hSM : ∀ m (h : Hist (Bits k n) α Bool m), M ≤ pullCount σ (Batch.ofFin u) h →
      (⟨m, h⟩ : Σ m, Hist (Bits k n) α Bool m) ∈ (reducedAlg ρ τ B).stopSet :=
    fun m h hM ↦ hB m (Hist.map (liftBits ρ τ) id boolLoss h) hM
  rw [outputMeasure_comapBanditFeedback_strategyOn hσρ hττ', IdentAlg.outputMeasure,
    stoppedHistMeasure_redStrategy_eq_comp w M _ (reducedAlg ρ τ B).measurableSet_stopSet hSM,
    Measure.comp_assoc, recordOutputKernel, Measure.comap_comp]
  congr 1
  rw [recordLaw, Measure.pi_map_pi (fun _ ↦ measurable_recordOf.aemeasurable)]

/-- **Data processing through the pull records** (`lem:events_before_pulls`). Let `B` be an
identification algorithm (with bandit feedback) on the general types that stops at the latest when
it has pulled batch `u` `M` times. The divergence between the laws of its output under the uniform
mixture of the strategies `S_(u, v)` and under `S_0` is at most the divergence between the uniform
mixture of the products `P_(1, v)^M` and `P_0^M` of the two-batch game. The bound holds for
every `ε`. -/
lemma klDiv_outputMeasure_le_klDiv_pi {𝓓 : Type*} [MeasurableSpace 𝓓]
    (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j) {ε : ℝ}
    (B : IdentAlg (ι → α) α ℝ 𝓓) (u : Fin k) (M : ℕ)
    (hB : ∀ m (h : Hist (ι → α) α ℝ m), M ≤ pullCount σ (some u : Batch k) h →
      (⟨m, h⟩ : Σ m, Hist (ι → α) α ℝ m) ∈ B.stopSet) :
    klDiv ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n,
        B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε (Expert.mk u v)))
      (B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε Expert.zero)) ≤
    klDiv ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n, Measure.pi fun _ : Fin M ↦ roundLaw ε (Expert.mk 0 v))
      (Measure.pi fun _ : Fin M ↦ roundLaw (k := 1) ε Expert.zero) := by
  set K := recordOutputKernel σ ρ τ ε B u M
  have h_out := outputMeasure_eq_comp_pi_roundLaw hσρ hττ' ε B u M hB
  have h_mix : (n : ℝ≥0∞)⁻¹ • ∑ v : Fin n,
      B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε (Expert.mk u v)) =
      K ∘ₘ ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n,
        Measure.pi fun _ : Fin M ↦ roundLaw ε (Expert.mk 0 v)) := by
    rw [Measure.comp_smul]
    congr 1
    have h_sum : ∀ s : Finset (Fin n), ∑ v ∈ s, K ∘ₘ
        (Measure.pi fun _ : Fin M ↦ roundLaw (k := 1) ε (Expert.mk 0 v)) =
        K ∘ₘ ∑ v ∈ s, Measure.pi fun _ : Fin M ↦ roundLaw (k := 1) ε (Expert.mk 0 v) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Measure.bind_zero_left]
      | insert v s hv ih => rw [Finset.sum_insert hv, Finset.sum_insert hv, ih, Measure.comp_add]
    rw [← h_sum]
    exact Finset.sum_congr rfl fun v _ ↦ h_out (some v)
  have h_zero := h_out none
  simp only [batchExpert_none] at h_zero
  rw [h_mix, h_zero]
  have : IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n,
      Measure.pi fun _ : Fin M ↦ roundLaw (k := 1) ε (Expert.mk 0 v)) := by
    constructor
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, smul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]
      exact ENNReal.one_lt_top
  exact klDiv_comp_right_le _ _ K

end Chase2026Tight
