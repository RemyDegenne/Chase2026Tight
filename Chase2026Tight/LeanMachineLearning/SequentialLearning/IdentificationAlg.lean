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
* `Learning.IdentAlg.measurable_stoppedHist`, `Learning.IdentAlg.measurableSet_lt_stoppingTime`:
  measurability of the stopped history and of the events `{t < τ}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {A : IdentAlg 𝓞 𝓐 𝓨 𝓓}
  {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω}

/-- The stopped history of measurable observation, action and feedback processes is
measurable. -/
lemma IdentAlg.measurable_stoppedHist (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) :
    Measurable (A.stoppedHist O X Y) :=
  measurable_stoppedValue_sigmaHistory hO hX hY
    (measurable_hittingAfter_sigmaHistory hO hX hY A.measurableSet_stopSet)

/-- For measurable observation, action and feedback processes, the events `{t < τ}` for the
stopping time `τ` of an identification algorithm are measurable. -/
lemma IdentAlg.measurableSet_lt_stoppingTime (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < A.stoppingTime O X Y ω} :=
  measurable_hittingAfter_sigmaHistory hO hX hY A.measurableSet_stopSet
    (measurableSet_Ioi (a := (t : WithTop ℕ)))

/-- The probability that the output of `A` in `env` belongs to `s` is the expectation, along any
algorithm-environment sequence of the sampling rule `A.alg` in `env`, of the probability of `s`
under the output rule applied to the stopped history. -/
lemma IdentAlg.outputMeasure_apply_eq_lintegral [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y A.alg env P) {s : Set 𝓓} (hs : MeasurableSet s) :
    A.outputMeasure env s = ∫⁻ ω, A.output (A.stoppedHist O X Y ω) s ∂P := by
  rw [IdentAlg.outputMeasure, Measure.bind_apply hs A.output.measurable.aemeasurable,
    ← (h.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).map_eq]
  exact lintegral_map (A.output.measurable_coe hs)
    (IdentAlg.measurable_stoppedHist h.measurable_obs h.measurable_action h.measurable_feedback)

end Learning
