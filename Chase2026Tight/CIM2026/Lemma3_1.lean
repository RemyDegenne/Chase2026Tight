/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting

/-!
# Lemma 3.1: reduction from special batch identification to the bandit with expert advice

A learner whose pseudo-regret is at most `r T` after `T` rounds under every strategy of the pool
yields a good SBI algorithm which plays at most `T⋆` rounds, for any `T⋆ ≥ 1000 r(T⋆) / ε`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal

universe u

namespace Chase2026Tight

/-- **Lemma 3.1** (reduction from SBI to BwE, Chase, Ito, Mehalel 2026). Let `alg` be a learner
for the bandit with expert advice whose pseudo-regret under every strategy `S_θ` of the pool is
at most `r T` after `T` rounds, for all `T`, and let `T⋆ ≥ 1000 r(T⋆) / ε`. Then there is a good
SBI algorithm whose expected number of rounds under every strategy of the pool is at most
`T⋆`. The paper's `T⋆ ≥ 1` (implicit: its proof divides by `T⋆`) is made explicit: for
`T⋆ = 0` and `r = id` the hypotheses hold while no good algorithm stops after `0` rounds. -/
theorem exists_isGood_expectedRounds_le (k n : ℕ) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1)
    (alg : Algorithm (Expert k n → Arm k) (Arm k) ℝ) (r : ℕ → ℝ)
    (hr : ∀ (θ : Expert k n) (T : ℕ) {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → Expert k n → Arm k)
      (A : ℕ → Ω → Arm k) (Y : ℕ → Ω → Arm k → ℝ),
      IsAlgEnvSeq O A Y alg.comapBanditFeedback (strategy ε θ) P →
        expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T ≤ r T)
    {T : ℕ} (hT1 : 1 ≤ T) (hT : 1000 * r T / ε ≤ T) :
    ∃ A' : SBIAlg k n, IsGood ε A' ∧
      ∀ (θ : Expert k n) {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
        [IsProbabilityMeasure P] (O : ℕ → Ω → Expert k n → Arm k) (X : ℕ → Ω → Arm k)
        (Y : ℕ → Ω → Arm k → ℝ) (out : Ω → Batch k),
        A'.toIdentAlg.IsRun (strategy ε θ) O X Y out P →
          expectedRounds A' O X Y P ≤ T := by
  sorry

end Chase2026Tight
