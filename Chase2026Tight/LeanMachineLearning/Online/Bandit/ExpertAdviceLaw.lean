/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.LeanMachineLearning.Online.Bandit.ExpertAdvice

/-!
# The pseudo-regret depends only on the learner and the adversary

The pseudo-regret `expertPseudoRegret` of a run of a learner against an adversary is an
expectation of a function of the trajectory of the run, whose law is determined by the learner and
the adversary (LML's `isAlgEnvSeq_unique`). Hence all the runs of a learner against an adversary,
possibly on different probability spaces, have the same pseudo-regret.

## Main statements

* `Bandits.expertPseudoRegret_eq_of_isAlgEnvSeq`: two runs have the same pseudo-regret.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Bandits

variable {α ι 𝓞 Ω Ω' : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]
  {m𝓞 : MeasurableSpace 𝓞} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {alg : Algorithm 𝓞 α (α → ℝ)} {env : Environment 𝓞 α (α → ℝ)}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → α → ℝ}
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → α}
  {Y' : ℕ → Ω' → α → ℝ}

/-- The pseudo-regret of a run of a learner against an adversary depends only on the learner and
the adversary: two runs, possibly on different probability spaces, have the same pseudo-regret.
The advice vectors are read from the observations through a measurable map `π` (for
deterministic advice, `π = diracAdvice`). -/
lemma expertPseudoRegret_eq_of_isAlgEnvSeq (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg env P') {π : 𝓞 → Advice ι α} (hπ : Measurable π) (T : ℕ) :
    expertPseudoRegret P (fun t ω ↦ π (O t ω)) A Y T =
      expertPseudoRegret P' (fun t ω ↦ π (O' t ω)) A' Y' T := by
  unfold expertPseudoRegret
  congr 1
  ext j
  let F : (ℕ → Round 𝓞 α (α → ℝ)) → ℝ := fun h ↦
    adviceRegret (fun t ↦ π (h t).obs) (fun t ↦ (h t).action) (fun t ↦ (h t).feedback) T j
  have hF : Measurable F := by
    refine (Finset.measurable_sum _ fun t _ ↦ ?_).sub (Finset.measurable_sum _ fun t _ ↦ ?_)
    · exact (Round.measurable_feedback.comp (measurable_pi_apply t)).eval_prod
        (Round.measurable_action.comp (measurable_pi_apply t))
    · exact measurable_expertLoss (hπ.comp (Round.measurable_obs.comp (measurable_pi_apply t)))
        (Round.measurable_feedback.comp (measurable_pi_apply t)) j
  change ∫ ω, F (trajectory O A Y ω) ∂P = ∫ ω, F (trajectory O' A' Y' ω) ∂P'
  rw [← integral_map h.measurable_trajectory.aemeasurable hF.aestronglyMeasurable,
    ← integral_map h'.measurable_trajectory.aemeasurable hF.aestronglyMeasurable,
    isAlgEnvSeq_unique h h']

end Bandits
