/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.RoundLaw
public import Chase2026Tight.Mathlib.InformationTheory.KullbackLeibler.Mixture

/-!
# Lemma 4.1: KL bound between the mixture and the null in the two-batch game

In the two-batch game (`k = 1`), the learner always pulls an arm of batch `1`, so that the advice
and losses of the rounds are i.i.d. with law `P_θ = roundLaw ε θ` under `S_θ`. The
Kullback–Leibler divergence between the uniform mixture over `v` of `P_(1, v)^T` and `P_0^T` is
at most `((1 + 4 ε²)^T - 1) / n`.

The proof bounds the divergence by the χ² divergence of the mixture
(`InformationTheory.klDiv_sum_smul_withDensity_le`):
`KL(P_mix^T ‖ P_0^T) ≤ (1/n²) ∑_{v, w} E_{P_(1, w)^T}[dP_(1, v)^T/dP_0^T] - 1`, and the expected
likelihood ratios are `(1 + 4ε²)^T` for `v = w` and `1` otherwise (`lintegral_prod_roundDensity`).
The paper's proof (Jensen's inequality for the concave `log`, then `log(1 + x) ≤ x`) reaches the
same bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

/-- `∑_v ∑_w (1/n²) (if w = v then b else 1) = 1 + (b - 1)/n`. -/
lemma sum_sum_inv_mul_inv_mul_ite {n : ℕ} (hn : 1 ≤ n) (b : ℝ) :
    ∑ v : Fin n, ∑ w : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * (if w = v then b else 1) =
      1 + (b - 1) / n := by
  have h (v : Fin n) : ∑ w : Fin n, (if w = v then b else 1) = n + (b - 1) := by
    have : ∀ w : Fin n, (if w = v then b else 1) = 1 + if w = v then b - 1 else 0 := by
      intro w; split_ifs <;> ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp
  simp_rw [← Finset.mul_sum, h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

-- The frozen statement keeps the paper's unused hypothesis `T ≥ 1`.
set_option linter.unusedVariables false in
/-- **Lemma 4.1** (Chase, Ito, Mehalel 2026; Ito et al. 2024). In the two-batch game (`k = 1`),
for `0 < ε ≤ 0.1`, `T ≥ 1` and `n ≥ 1`,
`KL((1/n) ∑_v P_(1, v)^T ‖ P_0^T) ≤ ((1 + 4 ε²)^T - 1) / n`. The hypothesis `T ≥ 1` of the paper
is not needed (the bound holds for `T = 0`); it is kept in the statement, as in the paper. -/
@[nolint unusedArguments]
theorem klDiv_mixture_pi_roundLaw_le {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1)
    {T : ℕ} (hT : 1 ≤ T) :
    klDiv ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n, Measure.pi fun _ : Fin T ↦ roundLaw ε (Expert.mk 0 v))
        (Measure.pi fun _ : Fin T ↦ roundLaw (k := 1) ε Expert.zero) ≤
      ENNReal.ofReal (((1 + 4 * ε ^ 2) ^ T - 1) / n) := by
  obtain ⟨hε0, hε1⟩ := hε
  replace hε0 : 0 ≤ ε := hε0.le
  replace hε1 : ε ≤ 1 / 2 := by linarith
  -- the mixture of the `P_(1, v)^T = P_0^T.withDensity (∏_t f_v(g_t))`, by its χ² divergence
  simp_rw [pi_roundLaw_mk_eq_withDensity hε0 hε1 _ T, Finset.smul_sum]
  refine (klDiv_sum_smul_withDensity_le (fun v ↦ by fun_prop) (fun v ↦ ?_) ?_).trans ?_
  · rw [lintegral_fintype_prod_eq_pow (measurable_roundDensity ε v),
      lintegral_roundDensity_zero hε0 hε1, one_pow]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp; omega) (ENNReal.natCast_ne_top n)
  -- the expected likelihood ratios
  simp_rw [← pi_roundLaw_mk_eq_withDensity hε0 hε1 _ T, lintegral_prod_roundDensity hε0 hε1]
  have h_inv : (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal (n : ℝ)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  have h_sum : ∑ v : Fin n, ∑ w : Fin n, (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ *
      (if w = v then ENNReal.ofReal ((1 + 4 * ε ^ 2) ^ T) else 1) =
      ENNReal.ofReal (∑ v : Fin n, ∑ w : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
        (if w = v then (1 + 4 * ε ^ 2) ^ T else 1)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ Finset.sum_nonneg fun w _ ↦ by positivity)]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun w _ ↦ by positivity)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), h_inv]
    split_ifs <;> simp
  have h_le : 1 ≤ (1 + 4 * ε ^ 2) ^ T := one_le_pow₀ (by nlinarith)
  have h_nonneg : 0 ≤ ((1 + 4 * ε ^ 2) ^ T - 1) / n := by
    have : 0 ≤ (1 + 4 * ε ^ 2) ^ T - 1 := by linarith
    positivity
  rw [h_sum, sum_sum_inv_mul_inv_mul_ite hn, ENNReal.ofReal_add zero_le_one h_nonneg,
    ENNReal.ofReal_one, ENNReal.add_sub_cancel_left ENNReal.one_ne_top]

end Chase2026Tight
