/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Comap
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Runs of relabelled algorithms and environments

LML's `Algorithm.congr` and `Environment.congr` relabel the observations, actions and feedbacks
of an algorithm and an environment along measurable equivalences. Relabelling a run gives a run
of the relabelled pair (`IsAlgEnvSeq.congr_measurableEquiv`).

As a consequence, if the observation, action and feedback spaces are measurably equivalent to
spaces in a universe `Type u`, then every algorithm has a run in every environment on a probability
space in `Type u` (`exists_isAlgEnvSeq_of_measurableEquiv`), whatever the universes of the spaces
themselves: the canonical space of the relabelled pair (`trajMeasure`), with the processes
relabelled back. This is useful to apply a hypothesis quantified over the runs on probability
spaces in a fixed universe, for spaces in other universes (finite types, `α → ℝ` for a finite
type `α`, ...).

## Main statements

* `Learning.IsAlgEnvSeq.congr_measurableEquiv`: relabelling of a run.
* `Learning.exists_isAlgEnvSeq_of_measurableEquiv`: existence of a run in a given universe.
* `Learning.exists_isAlgEnvSeq_of_finite`: existence of a run in any universe for finite
  observations and actions and feedback vectors indexed by the actions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓐 𝓐' 𝓨 𝓨' Ω : Type*}
  {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓐' : MeasurableSpace 𝓐'}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓨' : MeasurableSpace 𝓨'}
  {mΩ : MeasurableSpace Ω}

/-- Relabelling a history along measurable equivalences, then back, gives the history. -/
@[simp]
lemma Hist.map_symm_map (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐') (e𝓨 : 𝓨 ≃ᵐ 𝓨') {n : ℕ}
    (h : Hist 𝓞 𝓐 𝓨 n) :
    Hist.map e𝓞.symm e𝓐.symm e𝓨.symm (Hist.map e𝓞 e𝓐 e𝓨 h) = h := by
  funext i
  simp [Hist.map, Round.map]

/-- **Relabelling of a run.** Relabelling the observations, actions and feedbacks of a run of
`alg` in `env` along measurable equivalences gives a run of the relabelled algorithm in the
relabelled environment. -/
lemma IsAlgEnvSeq.congr_measurableEquiv {P : Measure Ω} [IsFiniteMeasure P]
    {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
    (h : IsAlgEnvSeq O A Y alg env P) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐') (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    IsAlgEnvSeq (fun n ω ↦ e𝓞 (O n ω)) (fun n ω ↦ e𝓐 (A n ω)) (fun n ω ↦ e𝓨 (Y n ω))
      (alg.congr e𝓞 e𝓐 e𝓨) (env.congr e𝓞 e𝓐 e𝓨) P where
  measurable_obs n := e𝓞.measurable.comp (h.measurable_obs n)
  measurable_action n := e𝓐.measurable.comp (h.measurable_action n)
  measurable_feedback n := e𝓨.measurable.comp (h.measurable_feedback n)
  hasCondDistrib_obs n := by
    have h1 := (h.hasCondDistrib_obs n).comp_left e𝓞.measurable
    have h_eq : (env.obs n).map e𝓞 = ((env.congr e𝓞 e𝓐 e𝓨).obs n).comap
        (Hist.map e𝓞 e𝓐 e𝓨) (by fun_prop) := by
      ext p : 1
      rw [Kernel.comap_apply, Environment.obs_congr, Kernel.comap_apply, Hist.map_symm_map]
    rw [h_eq] at h1
    exact h1.comp_right
  hasCondDistrib_action n := by
    have h1 := (h.hasCondDistrib_action n).comp_left e𝓐.measurable
    have h_eq : (alg.policy n).map e𝓐 = ((alg.congr e𝓞 e𝓐 e𝓨).policy n).comap
        (fun p ↦ (Hist.map e𝓞 e𝓐 e𝓨 p.1, e𝓞 p.2)) (by fun_prop) := by
      ext p : 1
      rw [Kernel.comap_apply, Algorithm.policy_congr, Kernel.comap_apply, Hist.map_symm_map,
        MeasurableEquiv.symm_apply_apply]
    rw [h_eq] at h1
    exact h1.comp_right
  hasCondDistrib_feedback n := by
    have h1 := (h.hasCondDistrib_feedback n).comp_left e𝓨.measurable
    have h_eq : (env.feedback n).map e𝓨 = ((env.congr e𝓞 e𝓐 e𝓨).feedback n).comap
        (fun p ↦ ((Hist.map e𝓞 e𝓐 e𝓨 p.1.1, e𝓞 p.1.2), e𝓐 p.2)) (by fun_prop) := by
      ext p : 1
      rw [Kernel.comap_apply, Environment.feedback_congr, Kernel.comap_apply, Hist.map_symm_map,
        MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_apply_apply]
    rw [h_eq] at h1
    exact h1.comp_right

universe u

/-- **Runs in a given universe.** If the observation, action and feedback spaces are measurably
equivalent to spaces in `Type u`, then every algorithm has a run in every environment on a
probability space in `Type u`. -/
lemma exists_isAlgEnvSeq_of_measurableEquiv {𝓞' 𝓐' 𝓨' : Type u} [MeasurableSpace 𝓞']
    [MeasurableSpace 𝓐'] [MeasurableSpace 𝓨'] (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐') (e𝓨 : 𝓨 ≃ᵐ 𝓨')
    (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨), IsAlgEnvSeq O A Y alg env P := by
  have h := (IT.isAlgEnvSeq_trajMeasure (alg.congr e𝓞 e𝓐 e𝓨)
    (env.congr e𝓞 e𝓐 e𝓨)).congr_measurableEquiv e𝓞.symm e𝓐.symm e𝓨.symm
  rw [Algorithm.congr_symm, Environment.congr_symm] at h
  exact ⟨_, _, _, inferInstance, _, _, _, h⟩

/-- **Runs in a given universe, finite observations and actions.** If the observations and the
actions are finite (with measurable singletons) and the feedbacks are vectors `𝓐 → 𝓩` indexed by
the actions with `𝓩 : Type` (for instance loss vectors, `𝓩 = ℝ`), then every algorithm has a run
in every environment on a probability space in `Type u`, for every universe `u`. -/
lemma exists_isAlgEnvSeq_of_finite {𝓩 : Type} [MeasurableSpace 𝓩] [Finite 𝓞]
    [MeasurableSingletonClass 𝓞] [Finite 𝓐] [MeasurableSingletonClass 𝓐]
    (alg : Algorithm 𝓞 𝓐 (𝓐 → 𝓩)) (env : Environment 𝓞 𝓐 (𝓐 → 𝓩)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓐 → 𝓩), IsAlgEnvSeq O A Y alg env P := by
  obtain ⟨nO, ⟨eO⟩⟩ := Finite.exists_equiv_fin 𝓞
  obtain ⟨nA, ⟨eA⟩⟩ := Finite.exists_equiv_fin 𝓐
  let mO : 𝓞 ≃ᵐ ULift.{u} (Fin nO) :=
    (⟨eO, measurable_of_countable _, measurable_of_countable _⟩ : 𝓞 ≃ᵐ Fin nO).trans
      MeasurableEquiv.ulift.symm
  let mA : 𝓐 ≃ᵐ ULift.{u} (Fin nA) :=
    (⟨eA, measurable_of_countable _, measurable_of_countable _⟩ : 𝓐 ≃ᵐ Fin nA).trans
      MeasurableEquiv.ulift.symm
  let mY : (𝓐 → 𝓩) ≃ᵐ ULift.{u} (Fin nA → 𝓩) :=
    (MeasurableEquiv.piCongrLeft (fun _ ↦ 𝓩) eA.symm).symm.trans MeasurableEquiv.ulift.symm
  exact exists_isAlgEnvSeq_of_measurableEquiv mO mA mY alg env

end Learning
