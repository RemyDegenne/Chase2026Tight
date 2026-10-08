/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Compositions with kernels read through maps

* `Measure.comap_comp`: `κ.comap f ∘ₘ μ = κ ∘ₘ μ.map f`.
* `HasCondDistrib.map_of_forall_eq`: if `Y` has conditional distribution `κ` given `X`, then
  `F X Y` has conditional distribution `x ↦ (κ x).map (F x)` given `X`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Composing a measure with a kernel read through a measurable map is composing the image measure
with the kernel. -/
lemma _root_.MeasureTheory.Measure.comap_comp {α β γ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : Kernel β γ) {f : α → β}
    (hf : Measurable f) (μ : Measure α) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) hf]
  rfl

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}

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
