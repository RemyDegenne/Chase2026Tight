/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The Kullback–Leibler divergence is bounded by the χ² divergence; finite mixtures

For probability measures `μ ≪ ν`, `KL(μ ‖ ν) ≤ χ²(μ ‖ ν) = ∫ (dμ/dν)² dν - 1`: pointwise,
`klFun x = x log x + 1 - x ≤ (x - 1)²` for `x ≥ 0` (since `log x ≤ x - 1`), and
`∫ (dμ/dν - 1)² dν = ∫ (dμ/dν)² dν - 1`.

For a finite mixture `∑ i, w i • P i` of probability measures `P i = ν.withDensity (f i)`, the
χ² divergence expands into `∑ i, ∑ j, w i * w j * ∫ f j dP i - 1`, where `∫ f j dP i` is the
expectation under `P i` of the likelihood ratio `dP j/dν`.

## Main statements

* `InformationTheory.klDiv_le_lintegral_rnDeriv_sq_sub_one`: `KL(μ ‖ ν) ≤ ∫ (dμ/dν)² dν - 1`.
* `InformationTheory.klDiv_withDensity_le`: `KL(ν.withDensity f ‖ ν) ≤ ∫ f² dν - 1`.
* `InformationTheory.klDiv_sum_smul_withDensity_le`: the bound for a finite mixture,
  `KL(∑ i, w i • P i ‖ ν) ≤ ∑ i, ∑ j, w i * w j * ∫ f j dP i - 1`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- `klFun x = x log x + 1 - x` is at most `(x - 1)²` for `x ≥ 0`. -/
lemma klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) : klFun x ≤ (x - 1) ^ 2 := by
  rw [klFun_apply]
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
  nlinarith

/-- For a finite `x : ℝ≥0∞`, `(x - 1)² + 2 x = x² + 1`. -/
lemma _root_.ENNReal.ofReal_sq_toReal_sub_one_add_two_mul {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ENNReal.ofReal ((x.toReal - 1) ^ 2) + 2 * x = x ^ 2 + 1 := by
  lift x to NNReal using hx
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [ENNReal.toReal_ofReal (NNReal.coe_nonneg x)]
  rw [← ENNReal.ofReal_pow (NNReal.coe_nonneg x), ← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _) (by positivity),
    ← ENNReal.ofReal_add (by positivity) zero_le_one]
  congr 1
  ring

/-- **The Kullback–Leibler divergence is bounded by the χ² divergence**: for probability measures
`μ ≪ ν`, `KL(μ ‖ ν) ≤ ∫ (dμ/dν)² dν - 1`. -/
lemma klDiv_le_lintegral_rnDeriv_sq_sub_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    klDiv μ ν ≤ ∫⁻ x, μ.rnDeriv ν x ^ 2 ∂ν - 1 := by
  rw [klDiv_eq_lintegral_klFun_of_ac hμν]
  have h_le : ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν ≤
      ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν :=
    lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one ENNReal.toReal_nonneg)
  refine h_le.trans (ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_)
  have h_eq : ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν + 2 =
      ∫⁻ x, μ.rnDeriv ν x ^ 2 ∂ν + 1 := by
    have h2 : (2 : ℝ≥0∞) = ∫⁻ x, 2 * μ.rnDeriv ν x ∂ν := by
      rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _),
        Measure.lintegral_rnDeriv hμν, measure_univ, mul_one]
    have h1 : (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂ν := by simp
    rw [h2, h1, ← lintegral_add_right _ (by fun_prop), ← lintegral_add_right _ (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    exact ENNReal.ofReal_sq_toReal_sub_one_add_two_mul hx
  have h_two : (2 : ℝ≥0∞) = 1 + 1 := by norm_num
  rw [h_two, ← add_assoc] at h_eq
  exact ((ENNReal.add_left_inj ENNReal.one_ne_top).mp h_eq).le

/-- The Kullback–Leibler divergence between `ν.withDensity f` and a probability measure `ν`, for a
probability density `f`, is at most `∫ f² dν - 1`. -/
lemma klDiv_withDensity_le [IsProbabilityMeasure ν] {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hf_one : ∫⁻ x, f x ∂ν = 1) :
    klDiv (ν.withDensity f) ν ≤ ∫⁻ x, f x ^ 2 ∂ν - 1 := by
  have : IsProbabilityMeasure (ν.withDensity f) := ⟨by simp [hf_one]⟩
  refine (klDiv_le_lintegral_rnDeriv_sq_sub_one (withDensity_absolutelyContinuous _ _)).trans_eq ?_
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ ν hf] with x hx
  rw [hx]

/-- **Divergence of a finite mixture.** Let `P i = ν.withDensity (f i)` be probability measures
(`∫ f i dν = 1`) and `w` weights summing to `1`. Then
`KL(∑ i, w i • P i ‖ ν) ≤ ∑ i, ∑ j, w i * w j * ∫ f j dP i - 1`, where `f j = dP j/dν`. -/
lemma klDiv_sum_smul_withDensity_le {ι : Type*} [Fintype ι] [IsProbabilityMeasure ν]
    {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hf_one : ∀ i, ∫⁻ x, f i x ∂ν = 1)
    {w : ι → ℝ≥0∞} (hw : ∑ i, w i = 1) :
    klDiv (∑ i, w i • ν.withDensity (f i)) ν ≤
      ∑ i, ∑ j, w i * w j * ∫⁻ x, f j x ∂(ν.withDensity (f i)) - 1 := by
  rw [finsetSum_smul_withDensity _ (fun i _ ↦ hf i)]
  refine (klDiv_withDensity_le (by fun_prop) ?_).trans_eq ?_
  · rw [lintegral_finsetSum' _ fun i _ ↦ ((hf i).const_mul _).aemeasurable]
    simp_rw [lintegral_const_mul _ (hf _), hf_one, mul_one, hw]
  · congr 1
    simp_rw [sq, Finset.sum_mul_sum]
    rw [lintegral_finsetSum' _ fun i _ ↦ by fun_prop]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lintegral_finsetSum' _ fun j _ ↦ by fun_prop]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ (hf i) (hf j),
      ← lintegral_const_mul _ (by fun_prop)]
    congr with x
    simp only [Pi.mul_apply]
    ring

end InformationTheory
