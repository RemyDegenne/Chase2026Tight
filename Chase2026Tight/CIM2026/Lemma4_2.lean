/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.LowerBound

/-!
# Lemma 4.2: lower bound for the two-batch game

In the two-batch game (`k = 1`), a good SBI algorithm plays at least `ln(n / 10) / (8 ε²)` rounds
in expectation under `S_0`. This is the case `k = 1`, identity maps, of the general bound
`ofReal_le_lintegral_stoppingTime` (with `ln(1 + n/8) ≥ ln(n/10)`).
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
  have h' : A'.comapBanditFeedback.IsRun
      (strategyOn (α := Arm 1) (ι := Expert 1 n) id id id id ε Expert.zero) O X Y out P := by
    rw [strategyOn_id]
    exact h
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_le_lintegral_stoppingTime
    (fun _ ↦ rfl) (fun _ ↦ rfl) hε (by omega) ((isGoodOn_id ε A').2 hA') h')
  rw [Nat.cast_one, one_mul]
  have := hε.1
  exact div_le_div_of_nonneg_right (log_div_ten_le_log_one_add_div_eight hn) (by positivity)

end Chase2026Tight
