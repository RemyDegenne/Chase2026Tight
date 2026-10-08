/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Composition of a measure and a kernel read through a map

## Main statements

* `MeasureTheory.Measure.comap_comp`: `κ.comap f ∘ₘ μ = κ ∘ₘ μ.map f`.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Composing a measure with a kernel read through a measurable map is composing the image measure
with the kernel. -/
lemma comap_comp (κ : Kernel β γ) {f : α → β} (hf : Measurable f) (μ : Measure α) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) hf]
  rfl

end MeasureTheory.Measure
