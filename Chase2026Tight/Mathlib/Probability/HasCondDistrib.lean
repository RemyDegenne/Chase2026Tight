/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Conditional distributions: composition with a measure-preserving map, composition-products

## Main statements

* `ProbabilityTheory.HasCondDistrib.comp_measurePreserving`: a conditional distribution is
  preserved by composing both random variables with a measure-preserving map.
* `ProbabilityTheory.hasCondDistrib_snd_fst_compProd`: under `μ ⊗ₘ κ`, the second coordinate has
  conditional distribution `κ` given the first one.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨} {f : Ω' → Ω}

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

end ProbabilityTheory
