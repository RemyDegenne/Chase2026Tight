/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Conditional distributions: measure-preserving maps, composition-products, images

## Main statements

* `ProbabilityTheory.HasCondDistrib.comp_measurePreserving`: a conditional distribution is
  preserved by composing both random variables with a measure-preserving map.
* `ProbabilityTheory.hasCondDistrib_snd_fst_compProd`: under `μ ⊗ₘ κ`, the second coordinate has
  conditional distribution `κ` given the first one.
* `ProbabilityTheory.HasCondDistrib.map_of_forall_eq`: if `Y` has conditional distribution `κ`
  given `X`, then `F X Y` has conditional distribution `x ↦ (κ x).map (F x)` given `X`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨} {f : Ω' → Ω}

/-- A conditional distribution is preserved by composing both random variables with a
measure-preserving map. -/
lemma HasCondDistrib.comp_measurePreserving (h : HasCondDistrib Y X κ P)
    (hf : MeasurePreserving f P' P) :
    HasCondDistrib (Y ∘ f) (X ∘ f) κ P' := by
  have hX : AEMeasurable X (P'.map f) := hf.map_eq ▸ h.aemeasurable_fst
  have h_map : P'.map (X ∘ f) = P.map X := by
    rw [← AEMeasurable.map_map_of_aemeasurable hX hf.measurable.aemeasurable, hf.map_eq]
  unfold HasCondDistrib
  rw [h_map]
  exact h.comp hf.hasLaw

/-- Under `μ ⊗ₘ κ`, the second coordinate has conditional distribution `κ` given the first one. -/
lemma hasCondDistrib_snd_fst_compProd (μ : Measure 𝓧) [IsFiniteMeasure μ] (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] :
    HasCondDistrib Prod.snd Prod.fst κ (μ ⊗ₘ κ) where
  aemeasurable := measurable_id.aemeasurable
  map_eq := by
    rw [← Measure.fst, Measure.fst_compProd]
    exact Measure.map_id

/-- If `Y` has conditional distribution `κ` given `X`, then `F X Y` has conditional distribution
`η` given `X`, for any kernel `η` with `η x = (κ x).map (F x)`. -/
lemma HasCondDistrib.map_of_forall_eq [SFinite P] [IsSFiniteKernel κ] {η : Kernel 𝓧 𝓩}
    [IsSFiniteKernel η] (h : HasCondDistrib Y X κ P) {F : 𝓧 → 𝓨 → 𝓩}
    (hF : Measurable (Function.uncurry F)) (hη : ∀ x, η x = (κ x).map (F x)) :
    HasCondDistrib (fun ω ↦ F (X ω) (Y ω)) X η P := by
  have hX : AEMeasurable X P := h.aemeasurable_fst
  have hY : AEMeasurable Y P := h.aemeasurable_snd
  have hT : Measurable (fun p : 𝓧 × 𝓨 ↦ (p.1, F p.1 p.2)) := measurable_fst.prodMk hF
  refine ⟨hX.prodMk (hF.comp_aemeasurable (hX.prodMk hY)), ?_⟩
  calc P.map (fun ω ↦ (X ω, F (X ω) (Y ω)))
  _ = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (p.1, F p.1 p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable hT.aemeasurable (hX.prodMk hY)]
    rfl
  _ = (P.map X ⊗ₘ κ).map (fun p ↦ (p.1, F p.1 p.2)) := by rw [h.map_eq]
  _ = P.map X ⊗ₘ η := by
    ext s hs
    rw [Measure.map_apply hT hs, Measure.compProd_apply (hT hs), Measure.compProd_apply hs]
    refine lintegral_congr fun x ↦ ?_
    have hFx : Measurable (F x) := hF.comp (measurable_prodMk_left (x := x))
    rw [hη x, Measure.map_apply hFx (measurable_prodMk_left hs)]
    rfl

end ProbabilityTheory
