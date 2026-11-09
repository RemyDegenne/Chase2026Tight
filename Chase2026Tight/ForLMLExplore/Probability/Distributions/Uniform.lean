/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.UniformOn

/-!
# The uniform law on a finite type: singletons, permutations, coordinates

The uniform law on a finite type `α` is `uniformOn Set.univ`.

## Main statements

* `ProbabilityTheory.uniformOn_univ_singleton`: the uniform law gives mass `1 / card α` to every
  point.
* `ProbabilityTheory.lintegral_uniformOn_univ_comp_equiv`: the uniform law is invariant under
  permutations: `∫ G ∘ σ = ∫ G` for every permutation `σ`.
* `ProbabilityTheory.uniformOn_univ_eval_eq`: under the uniform law on a finite type of functions
  `ι → β`, every coordinate is uniform.
* `ProbabilityTheory.uniformOn_univ_singleton_eq_mul`: the probability of a point `g` is the
  probability that the coordinates other than `i` agree with `g`, divided by `card β`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

section Singleton

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The uniform law on a finite type gives to a set the proportion of the points it contains. -/
lemma uniformOn_univ_apply_eq_card_div (s : Set α) [Fintype s] :
    uniformOn (Set.univ : Set α) s = Fintype.card s / Fintype.card α := by
  rw [uniformOn_univ, Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
  rfl

/-- The uniform law on a finite type gives mass `1 / card α` to every point. -/
lemma uniformOn_univ_singleton (a : α) :
    uniformOn (Set.univ : Set α) {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, ENNReal.div_eq_inv_mul, mul_one]

omit [Fintype α] in
/-- The uniform law on a finite type is invariant under permutations. -/
lemma lintegral_uniformOn_univ_comp_equiv [Finite α] (σ : α ≃ α) (G : α → ℝ≥0∞) :
    ∫⁻ x, G (σ x) ∂uniformOn Set.univ = ∫⁻ x, G x ∂uniformOn Set.univ := by
  have := Fintype.ofFinite α
  simp_rw [lintegral_fintype, uniformOn_univ_singleton]
  exact Equiv.sum_comp σ (fun x ↦ G x * _)

end Singleton

section Pi

variable {ι β : Type*} [Finite ι] [Fintype β]
  [MeasurableSpace (ι → β)] [MeasurableSingletonClass (ι → β)]

/-- The functions with a prescribed value at `i` are in bijection with pairs of a value at `i`
and a function with a prescribed value at `i`. -/
private def piEquivProdEval [DecidableEq ι] (i : ι) (x : β) :
    (ι → β) ≃ β × {f : ι → β // f i = x} where
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
private def equivUpdateEq [DecidableEq ι] (i : ι) (g : ι → β) :
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
lemma uniformOn_univ_eval_eq (i : ι) (x : β) :
    uniformOn (Set.univ : Set (ι → β)) {f | f i = x} = (Fintype.card β : ℝ≥0∞)⁻¹ := by
  classical
  have := Fintype.ofFinite ι
  rw [uniformOn_univ_apply_eq_card_div]
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
lemma uniformOn_univ_singleton_eq_mul [DecidableEq ι] [Nonempty β] (i : ι) (g : ι → β) :
    uniformOn (Set.univ : Set (ι → β)) {g} =
      uniformOn (Set.univ : Set (ι → β)) {f | Function.update f i (g i) = g} *
        (Fintype.card β : ℝ≥0∞)⁻¹ := by
  classical
  have := Fintype.ofFinite ι
  rw [uniformOn_univ_apply_eq_card_div, uniformOn_univ_apply_eq_card_div]
  have h1 : Fintype.card ({g} : Set (ι → β)) = 1 := by simp
  have h2 : Fintype.card {f : ι → β | Function.update f i (g i) = g} = Fintype.card β :=
    Fintype.card_congr (equivUpdateEq i g)
  rw [h1, h2, Nat.cast_one, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one, mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

end Pi

end ProbabilityTheory
