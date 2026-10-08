/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.Mathlib.Probability.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.IdentificationAlg

/-!
# Transport and existence of runs

Algorithm-environment sequences and runs of identification algorithms are statements about laws:
they are preserved by composition with a measure-preserving map
(`IsAlgEnvSeq.comp_measurePreserving`, `IdentAlg.IsRun.comp_measurePreserving`). Every
identification algorithm has a run in every environment, on a probability space in any (large
enough) universe (`IdentAlg.exists_isRun`): the canonical space of the trajectories
(`trajMeasure`) times the output space, with the output drawn from the output rule applied to the
stopped history, transported to a `ULift`.

## Main statements

* `Learning.IsAlgEnvSeq.comp_measurePreserving`,
  `Learning.IdentAlg.IsRun.comp_measurePreserving`: composition with a measure-preserving map.
* `Learning.IdentAlg.exists_isRun`: existence of a run.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

section Transport

variable {𝓞 𝓐 𝓨 𝓓 Ω Ω' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω' → Ω}

/-- An algorithm-environment sequence composed with a measure-preserving map is an
algorithm-environment sequence. -/
lemma IsAlgEnvSeq.comp_measurePreserving [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : IsAlgEnvSeq O X Y alg env P) (hf : MeasurePreserving f P' P) :
    IsAlgEnvSeq (fun n ↦ O n ∘ f) (fun n ↦ X n ∘ f) (fun n ↦ Y n ∘ f) alg env P' where
  measurable_obs n := (h.measurable_obs n).comp hf.measurable
  measurable_action n := (h.measurable_action n).comp hf.measurable
  measurable_feedback n := (h.measurable_feedback n).comp hf.measurable
  hasCondDistrib_obs n := (h.hasCondDistrib_obs n).comp_measurePreserving hf
  hasCondDistrib_action n := (h.hasCondDistrib_action n).comp_measurePreserving hf
  hasCondDistrib_feedback n := (h.hasCondDistrib_feedback n).comp_measurePreserving hf

/-- A run of an identification algorithm composed with a measure-preserving map is a run. -/
lemma IdentAlg.IsRun.comp_measurePreserving {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {out : Ω → 𝓓}
    [IsFiniteMeasure P] [IsFiniteMeasure P'] (h : A.IsRun env O X Y out P)
    (hf : MeasurePreserving f P' P) :
    A.IsRun env (fun n ↦ O n ∘ f) (fun n ↦ X n ∘ f) (fun n ↦ Y n ∘ f) (out ∘ f) P' where
  isAlgEnvSeq := h.isAlgEnvSeq.comp_measurePreserving hf
  hasCondDistrib_output := h.hasCondDistrib_output.comp_measurePreserving hf

end Transport

section Existence

universe u v₁ v₂ v₃ v₄

variable {𝓞 : Type v₁} {𝓐 : Type v₂} {𝓨 : Type v₃} {𝓓 : Type v₄} [MeasurableSpace 𝓞]
  [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace 𝓓]

/-- Every identification algorithm has a run in every environment, on a probability space in any
universe large enough to contain the observations, actions, feedbacks and outputs. -/
lemma IdentAlg.exists_isRun (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) :
    ∃ (Ω : Type max u v₁ v₂ v₃ v₄) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
      (out : Ω → 𝓓), A.IsRun env O X Y out P := by
  have hS : Measurable (A.stoppedHist (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
      IT.feedback) :=
    measurable_stoppedValue_sigmaHistory IT.measurable_obs IT.measurable_action
      IT.measurable_feedback (measurable_hittingAfter_sigmaHistory IT.measurable_obs
        IT.measurable_action IT.measurable_feedback A.measurableSet_stopSet)
  -- The run on the canonical space `(ℕ → Round 𝓞 𝓐 𝓨) × 𝓓`.
  set μ := trajMeasure A.alg env ⊗ₘ A.output.comap _ hS with hμ
  have h₀ : A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1)
      (fun n ω ↦ IT.feedback n ω.1) Prod.snd μ :=
    ⟨(IT.isAlgEnvSeq_trajMeasure A.alg env).comp_measurePreserving
      ⟨measurable_fst, by rw [hμ, ← Measure.fst, Measure.fst_compProd]⟩,
      (hasCondDistrib_snd_fst_compProd _ _).comp_right (hf := hS)⟩
  -- Its transport to the universe `max u v₁ v₂ v₃ v₄`.
  let e : ULift.{max u v₁ v₂ v₃ v₄} ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓓) ≃ᵐ ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓓) :=
    MeasurableEquiv.ulift
  have he : MeasurePreserving e (μ.map e.symm) μ :=
    (e.symm.measurable.measurePreserving μ).symm e.symm
  exact ⟨_, _, μ.map e.symm, inferInstance, _, _, _, _, h₀.comp_measurePreserving he⟩

end Existence

end Learning
