/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# The uniform law on a finite type: singletons and invariance under permutations

## Main statements

* `PMF.toMeasure_uniformOfFintype_singleton`: the uniform law gives mass `1 / card α` to every
  point.
* `PMF.lintegral_uniformOfFintype_comp_equiv`: the uniform law is invariant under permutations:
  `∫ G ∘ σ = ∫ G` for every permutation `σ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PMF

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The uniform law on a finite type gives mass `1 / card α` to every point. -/
lemma toMeasure_uniformOfFintype_singleton (a : α) :
    (uniformOfFintype α).toMeasure {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [toMeasure_apply_singleton _ _ (measurableSet_singleton _), uniformOfFintype_apply]

/-- The uniform law on a finite type is invariant under permutations. -/
lemma lintegral_uniformOfFintype_comp_equiv (σ : α ≃ α) (G : α → ℝ≥0∞) :
    ∫⁻ x, G (σ x) ∂(uniformOfFintype α).toMeasure = ∫⁻ x, G x ∂(uniformOfFintype α).toMeasure := by
  simp_rw [lintegral_fintype, toMeasure_uniformOfFintype_singleton]
  exact Equiv.sum_comp σ (fun x ↦ G x * _)

end PMF
