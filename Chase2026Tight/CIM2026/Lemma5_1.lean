/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.LowerBound

/-!
# Lemma 5.1: lower bound for the general SBI game

With `k + 1` batches, a good SBI algorithm plays at least `k ln(n / 10) / (20 ε²)` rounds in
expectation under `S_0`. This is the case of identity maps of the general bound
`ofReal_le_lintegral_stoppingTime`, `k ln(1 + n/8) / (8 ε²)`, with `ln(1 + n/8) ≥ ln(n/10)` and
`1/8 ≥ 1/20`.
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
  have h' : A'.comapBanditFeedback.IsRun
      (strategyOn (α := Arm k) (ι := Expert k n) id id id id ε Expert.zero) O X Y out P := by
    rw [strategyOn_id]
    exact h
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_le_lintegral_stoppingTime
    (fun _ ↦ rfl) (fun _ ↦ rfl) hε (by omega) ((isGoodOn_id ε A').2 hA') h')
  have hε0 := hε.1
  have hlog := log_div_ten_le_log_one_add_div_eight hn
  have hlog0 : 0 ≤ log (n / 10) := log_nonneg (by
    have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
    rw [le_div_iff₀ (by norm_num)]
    linarith)
  calc k * log (n / 10) / (20 * ε ^ 2) ≤ k * log (n / 10) / (8 * ε ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _ ≤ k * log (1 + n / 8) / (8 * ε ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity))
          (by positivity)

end Chase2026Tight
