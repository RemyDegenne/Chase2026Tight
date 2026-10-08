/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting

/-!
# Lemma 4.2: lower bound for the two-batch game

In the two-batch game (`k = 1`), a good SBI algorithm plays at least `ln(n / 10) / (8 ε²)` rounds
in expectation under `S_0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Real
open scoped ENNReal

universe u

namespace Chase2026Tight

/-- **Lemma 4.2** (lower bound for the two-batch game, Chase, Ito, Mehalel 2026). Let `k = 1`,
`0 < ε ≤ 0.1` and `n ≥ 10`. Every good SBI algorithm satisfies
`T(A', S_0) ≥ ln(n / 10) / (8 ε²)`. -/
theorem expectedRounds_ge_of_isGood_one {n : ℕ} (hn : 10 ≤ n) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1)
    (A' : SBIAlg 1 n) (hA' : IsGood ε A') {Ω : Type u} {_mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (O : ℕ → Ω → Expert 1 n → Arm 1) (X : ℕ → Ω → Arm 1)
    (Y : ℕ → Ω → Arm 1 → ℝ) (out : Ω → Batch 1)
    (h : A'.toIdentAlg.IsRun (strategy ε Expert.zero) O X Y out P) :
    ENNReal.ofReal (log (n / 10) / (8 * ε ^ 2)) ≤ expectedRounds A' O X Y P := by
  sorry

end Chase2026Tight
