/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting

/-!
# Lemma 5.1: lower bound for the general SBI game

With `k + 1` batches, a good SBI algorithm plays at least `k ln(n / 10) / (20 ε²)` rounds in
expectation under `S_0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Real
open scoped ENNReal

universe u

namespace Chase2026Tight

/-- **Lemma 5.1** (lower bound for the general SBI game, Chase, Ito, Mehalel 2026). For
`0 < ε ≤ 0.1` and `n ≥ 10`, every good SBI algorithm satisfies
`T(A', S_0) ≥ k ln(n / 10) / (20 ε²)`. -/
theorem expectedRounds_ge_of_isGood {k n : ℕ} (hn : 10 ≤ n) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1)
    (A' : SBIAlg k n) (hA' : IsGood ε A') {Ω : Type u} {_mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (O : ℕ → Ω → Expert k n → Arm k) (X : ℕ → Ω → Arm k)
    (Y : ℕ → Ω → Arm k → ℝ) (out : Ω → Batch k)
    (h : A'.toIdentAlg.IsRun (strategy ε Expert.zero) O X Y out P) :
    ENNReal.ofReal (k * log (n / 10) / (20 * ε ^ 2)) ≤ expectedRounds A' O X Y P := by
  sorry

end Chase2026Tight
