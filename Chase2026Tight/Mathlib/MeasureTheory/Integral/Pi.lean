/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Lebesgue integral of a product of functions of distinct coordinates

The `lintegral` version of `MeasureTheory.integral_fintype_prod_eq_prod`: on a finite product of
σ-finite measure spaces, the Lebesgue integral of `x ↦ ∏ i, f i (x i)` is the product of the
Lebesgue integrals of the measurable functions `f i`.

## Main statements

* `MeasureTheory.lintegral_fintype_prod_eq_prod`: Tonelli's theorem for a product of functions of
  distinct coordinates, in `n` variables indexed by a finite type.
* `MeasureTheory.lintegral_fintype_prod_eq_pow`: the same for a power of a measure.
-/

@[expose] public section

open Fintype
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

-- the option is needed as in the proof of `MeasureTheory.integral_fin_nat_prod_eq_prod`
set_option backward.isDefEq.respectTransparency false in
/-- A version of **Tonelli's theorem** in `n` variables, for a natural number `n`: the Lebesgue
integral of a product of measurable functions of distinct coordinates is the product of their
Lebesgue integrals. -/
lemma lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i ↦ hf i.succ), ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ ↦
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- A version of **Tonelli's theorem** with the variables indexed by a finite type: the Lebesgue
integral of a product of measurable functions of distinct coordinates is the product of their
Lebesgue integrals. -/
lemma lintegral_fintype_prod_eq_prod {E : ι → Type*} {f : (i : ι) → E i → ℝ≥0∞}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod fun i ↦ hf (e i)

/-- A version of **Tonelli's theorem** for a power of a measure: the Lebesgue integral of
`x ↦ ∏ i, f (x i)` is the power of the Lebesgue integral of `f`. -/
lemma lintegral_fintype_prod_eq_pow {E : Type*} {f : E → ℝ≥0∞} {mE : MeasurableSpace E}
    {μ : Measure E} [SigmaFinite μ] (hf : Measurable f) :
    ∫⁻ x : ι → E, ∏ i, f (x i) ∂(Measure.pi (fun _ ↦ μ)) = (∫⁻ x, f x ∂μ) ^ (card ι) := by
  rw [lintegral_fintype_prod_eq_prod fun _ ↦ hf, Finset.prod_const, card]

end MeasureTheory
