/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# The uniform law on a finite type: singletons, permutations, coordinates

## Main statements

* `PMF.toMeasure_uniformOfFintype_singleton`: the uniform law gives mass `1 / card α` to every
  point.
* `PMF.lintegral_uniformOfFintype_comp_equiv`: the uniform law is invariant under permutations:
  `∫ G ∘ σ = ∫ G` for every permutation `σ`.
* `PMF.toMeasure_uniformOfFintype_eval_eq`: under the uniform law on a finite type of functions
  `ι → β`, every coordinate is uniform.
* `PMF.toMeasure_uniformOfFintype_singleton_eq_mul`: the probability of a point `g` is the
  probability that the coordinates other than `i` agree with `g`, divided by `card β`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PMF

section Singleton

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

end Singleton

section Pi

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
  [MeasurableSpace (ι → β)] [MeasurableSingletonClass (ι → β)]

/-- The functions with a prescribed value at `i` are in bijection with pairs of a value at `i`
and a function with a prescribed value at `i`. -/
private def piEquivProdEval (i : ι) (x : β) : (ι → β) ≃ β × {f : ι → β // f i = x} where
  toFun f := (f i, ⟨Function.update f i x, by simp⟩)
  invFun p := Function.update p.2.1 i p.1
  left_inv f := by simp
  right_inv p := by
    obtain ⟨y, g, hg⟩ := p
    ext
    · simp
    · simp only [Function.update_idem]
      rw [← hg, Function.update_eq_self]

/-- The functions agreeing with `g` outside of `i` are in bijection with their values at `i`. -/
private def equivUpdateEq (i : ι) (g : ι → β) :
    {f : ι → β // Function.update f i (g i) = g} ≃ β where
  toFun f := f.1 i
  invFun y := ⟨Function.update g i y, by simp⟩
  left_inv f := by
    obtain ⟨f, hf⟩ := f
    ext j
    simp only
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, ← hf, Function.update_of_ne hj]
  right_inv y := by simp

/-- Under the uniform law on `ι → β`, every coordinate is uniform. -/
lemma toMeasure_uniformOfFintype_eval_eq (i : ι) (x : β) :
    (uniformOfFintype (ι → β)).toMeasure {f | f i = x} = (Fintype.card β : ℝ≥0∞)⁻¹ := by
  classical
  rw [toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  have h_card : Fintype.card (ι → β) = Fintype.card β * Fintype.card {f : ι → β | f i = x} := by
    rw [Fintype.card_congr (piEquivProdEval i x), Fintype.card_prod]
    rfl
  have : Nonempty {f : ι → β | f i = x} := ⟨⟨fun _ ↦ x, rfl⟩⟩
  have h_pos : Fintype.card {f : ι → β | f i = x} ≠ 0 := Fintype.card_ne_zero
  rw [h_card, Nat.cast_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast h_pos) (by simp), mul_one]

/-- Under the uniform law on `ι → β`, the probability of a point `g` is the probability that the
coordinates other than `i` agree with `g`, divided by the number of values of the coordinate `i`. -/
lemma toMeasure_uniformOfFintype_singleton_eq_mul (i : ι) (g : ι → β) :
    (uniformOfFintype (ι → β)).toMeasure {g} =
      (uniformOfFintype (ι → β)).toMeasure {f | Function.update f i (g i) = g} *
        (Fintype.card β : ℝ≥0∞)⁻¹ := by
  classical
  rw [toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet,
    toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  have h1 : Fintype.card ({g} : Set (ι → β)) = 1 := by simp
  have h2 : Fintype.card {f : ι → β | Function.update f i (g i) = g} = Fintype.card β :=
    Fintype.card_congr (equivUpdateEq i g)
  rw [h1, h2, Nat.cast_one, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one, mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

end Pi

end PMF
