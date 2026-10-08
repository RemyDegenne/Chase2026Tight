/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IdentificationAlg

/-!
# The law of the output of an identification algorithm along a run

The law `A.outputMeasure env` of the output of an identification algorithm is the output rule
integrated against the law of the stopped history, which is the law of the stopped history of any
algorithm-environment sequence of the sampling rule. Hence the probability of an event of the
output is the expectation, over any such sequence, of its probability under the output rule
applied to the stopped history.

## Main statements

* `Learning.IdentAlg.outputMeasure_apply_eq_lintegral`: `A.outputMeasure env s` is the integral
  of `A.output (A.stoppedHist O X Y ω) s` along any algorithm-environment sequence `O, X, Y`.
* `Learning.IdentAlg.measurableSet_lt_stoppingTime`: the events `{t < τ}` are measurable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {A : IdentAlg 𝓞 𝓐 𝓨 𝓓}
  {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω}

/-- The stopped history of an algorithm-environment sequence is measurable. -/
lemma IdentAlg.measurable_stoppedHist [IsFiniteMeasure P] {alg : Algorithm 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O X Y alg env P) :
    Measurable (A.stoppedHist O X Y) :=
  measurable_stoppedValue_sigmaHistory h.measurable_obs h.measurable_action h.measurable_feedback
    (measurable_hittingAfter_sigmaHistory h.measurable_obs h.measurable_action
      h.measurable_feedback A.measurableSet_stopSet)

/-- Along an algorithm-environment sequence, the events `{t < τ}` for the stopping time `τ` of an
identification algorithm are measurable. -/
lemma IdentAlg.measurableSet_lt_stoppingTime [IsFiniteMeasure P] {alg : Algorithm 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O X Y alg env P) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < A.stoppingTime O X Y ω} :=
  measurable_hittingAfter_sigmaHistory h.measurable_obs h.measurable_action
    h.measurable_feedback A.measurableSet_stopSet (measurableSet_Ioi (a := (t : WithTop ℕ)))

/-- The probability that the output of `A` in `env` belongs to `s` is the expectation, along any
algorithm-environment sequence of the sampling rule `A.alg` in `env`, of the probability of `s`
under the output rule applied to the stopped history. -/
lemma IdentAlg.outputMeasure_apply_eq_lintegral [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y A.alg env P) {s : Set 𝓓} (hs : MeasurableSet s) :
    A.outputMeasure env s = ∫⁻ ω, A.output (A.stoppedHist O X Y ω) s ∂P := by
  rw [IdentAlg.outputMeasure, Measure.bind_apply hs A.output.measurable.aemeasurable,
    ← (h.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).map_eq]
  exact lintegral_map (A.output.measurable_coe hs) (IdentAlg.measurable_stoppedHist h)

end Learning
