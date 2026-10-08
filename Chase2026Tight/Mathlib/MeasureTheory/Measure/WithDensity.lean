/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.Mathlib.MeasureTheory.Integral.Pi

/-!
# Measures with densities: images, finite mixtures and products

## Main statements

* `MeasureTheory.withDensity_map`: the measure with density `f` with respect to the image `g_* μ`
  is the image by `g` of the measure with density `f ∘ g` with respect to `μ`.
* `MeasureTheory.finsetSum_smul_withDensity`: a finite mixture of measures with densities with
  respect to `μ` has the mixture of the densities as density with respect to `μ`.
* `MeasureTheory.Measure.pi_withDensity`: the product of the measures `μ i` with densities `f i`
  is the product measure with density `x ↦ ∏ i, f i (x i)`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}

/-- The measure with density `f` with respect to the image measure `μ.map g` is the image by `g`
of the measure with density `f ∘ g` with respect to `μ`. -/
lemma withDensity_map {g : α → β} (hg : Measurable g) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.map g).withDensity f = (μ.withDensity (f ∘ g)).map g := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hg hs, withDensity_apply _ (hg hs),
    setLIntegral_map hs hf hg]
  rfl

/-- A finite mixture of measures with densities `f i` with respect to `μ`, with weights `w i`,
is the measure with density `∑ i, w i * f i` with respect to `μ`. -/
lemma finsetSum_smul_withDensity {ι : Type*} (s : Finset ι) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ s, Measurable (f i)) (w : ι → ℝ≥0∞) :
    ∑ i ∈ s, w i • μ.withDensity (f i) = μ.withDensity (fun x ↦ ∑ i ∈ s, w i * f i x) := by
  ext t ht
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ ht]
  rw [lintegral_finsetSum' _ fun i hi ↦ ((hf i hi).const_mul _).aemeasurable]
  exact Finset.sum_congr rfl fun i hi ↦ (lintegral_const_mul _ (hf i hi)).symm

/-- The product of the measures `μ i` with densities `f i` is the product measure
`Measure.pi μ` with density `x ↦ ∏ i, f i (x i)`. -/
lemma Measure.pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (Set.univ.pi s).indicator (fun x ↦ ∏ i, f i (x i)) =
      fun x ↦ ∏ i, (s i).indicator (f i) (x i) := by
    ext x
    by_cases h : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h]
      exact Finset.prod_congr rfl fun i _ ↦ (Set.indicator_of_mem (h i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem h]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [this, lintegral_fintype_prod_eq_prod fun i ↦ (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end MeasureTheory
