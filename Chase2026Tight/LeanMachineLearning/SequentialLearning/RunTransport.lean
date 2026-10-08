/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.LeanMachineLearning.SequentialLearning.PartialFeedback
public import Chase2026Tight.Mathlib.Probability.HasCondDistribComp

/-!
# Transport of runs and of output laws along history maps

Two ways of changing the spaces of an identification algorithm without changing the law of its
output.

* **Partial feedback.** If an algorithm `A` with feedback in `𝓦` is run as
  `A.comapPartialFeedback g` against an environment `env` with feedback in `𝓨`, of which it sees
  only `g (o, a, y)`, and if the kernels of `env` read the past rounds only through `g` (the
  observation kernels read the history seen through `g`, and the law of `g (o, a, y)` given the
  past rounds, `o` and `a` is a kernel `env'.feedback` of the history seen through `g`), then the
  output of `A.comapPartialFeedback g` in `env` has the law of the output of `A` in the
  environment `env'` on the partial feedbacks (`IdentAlg.outputMeasure_comapPartialFeedback`).
* **Relabelling along maps.** If `fo : 𝓞' → 𝓞` and `fy : 𝓨' → 𝓨` are measurable and the
  kernels of `env` on the histories transported by `fo` and `fy` are the images by `fo` and `fy`
  of the kernels of `env'`, then the output of `A` in `env` has the law of the output in `env'` of
  the algorithm `A.comapObsFeedback fo fy`, which reads its rounds through `fo` and `fy`
  (`IdentAlg.outputMeasure_comapObsFeedback`). The maps need not be injective nor measurable
  embeddings: a run in `env'` is transported to a run in `env`.

Both statements are proved by transporting a run (`IsAlgEnvSeq`) and the stopped history, whose
law is determined by the algorithm and the environment (LML's
`IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory`).

## Main definitions

* `IdentAlg.comapObsFeedback A fo fy`: the identification algorithm reading the observations
  through `fo` and the feedbacks through `fy`.

## Main statements

* `IsAlgEnvSeq.partialFeedback`, `IsAlgEnvSeq.mapObsFeedback`: transport of runs.
* `IdentAlg.outputMeasure_comapPartialFeedback`, `IdentAlg.outputMeasure_comapObsFeedback`:
  equality of the output laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓐 𝓨 𝓨' 𝓦 𝓩 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} {m𝓨' : MeasurableSpace 𝓨'}
  {m𝓦 : MeasurableSpace 𝓦} {m𝓩 : MeasurableSpace 𝓩} {mΩ : MeasurableSpace Ω}

/-! ### Stopped histories of related processes -/

section Stopped

variable {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω → 𝓞'} {Y' : ℕ → Ω → 𝓨'}

/-- If the histories of `(O', X, Y')` are the images of the histories of `(O, X, Y)` by maps
`G n`, the hitting time of a set `S` by the former is the hitting time of its preimage by the
latter. -/
lemma hittingAfter_sigmaHistory_preimage (G : ∀ n, Hist 𝓞 𝓐 𝓨 n → Hist 𝓞' 𝓐 𝓨' n)
    (hG : ∀ n ω, history O' X Y' n ω = G n (history O X Y n ω))
    (S : Set (Σ n, Hist 𝓞' 𝓐 𝓨' n)) :
    hittingAfter (sigmaHistory O X Y) (Sigma.map id G ⁻¹' S) 0 =
      hittingAfter (sigmaHistory O' X Y') S 0 := by
  have h : ∀ j ω, sigmaHistory O X Y j ω ∈ Sigma.map id G ⁻¹' S ↔
      sigmaHistory O' X Y' j ω ∈ S := by
    intro j ω
    simp [sigmaHistory, Sigma.map, hG]
  funext ω
  simp only [hittingAfter_def]
  split_ifs with h1 h2 h2
  · simp only [h] at h1 ⊢
  · simp only [h] at h1
    exact absurd h1 h2
  · simp only [h] at h1
    exact absurd h2 h1
  · rfl

/-- If the histories of `(O', X, Y')` are the images of the histories of `(O, X, Y)` by maps
`G n`, the stopped histories at any time `τ` are related by the same maps. -/
lemma sigmaMap_stoppedValue_sigmaHistory (G : ∀ n, Hist 𝓞 𝓐 𝓨 n → Hist 𝓞' 𝓐 𝓨' n)
    (hG : ∀ n ω, history O' X Y' n ω = G n (history O X Y n ω)) (τ : Ω → WithTop ℕ) (ω : Ω) :
    Sigma.map id G (stoppedValue (sigmaHistory O X Y) τ ω) =
      stoppedValue (sigmaHistory O' X Y') τ ω := by
  simp [stoppedValue, sigmaHistory, Sigma.map, hG]

/-- **Transport of the law of the stopped history.** Let `(O, X, Y)` be a run of `alg` in `env`
and `(O', X, Y')` a run of `alg'` in `env'` on the same probability space, whose histories are
the images of the histories of `(O, X, Y)` by measurable maps `G n`. The law of the history of
`(O', X, Y')` stopped by `S` is the image by `G` of the law of the history of `(O, X, Y)` stopped
by the preimage of `S`. -/
lemma map_stoppedHistMeasure_of_history_eq {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    {alg' : Algorithm 𝓞' 𝓐 𝓨'} {env' : Environment 𝓞' 𝓐 𝓨'} {P : Measure Ω}
    [IsProbabilityMeasure P] (h : IsAlgEnvSeq O X Y alg env P)
    (h' : IsAlgEnvSeq O' X Y' alg' env' P) (G : ∀ n, Hist 𝓞 𝓐 𝓨 n → Hist 𝓞' 𝓐 𝓨' n)
    (hGm : ∀ n, Measurable (G n)) (hG : ∀ n ω, history O' X Y' n ω = G n (history O X Y n ω))
    {S : Set (Σ n, Hist 𝓞' 𝓐 𝓨' n)} (hS : MeasurableSet S) :
    (stoppedHistMeasure alg env (Sigma.map id G ⁻¹' S)).map (Sigma.map id G) =
      stoppedHistMeasure alg' env' S := by
  have hSG : MeasurableSet (Sigma.map id G ⁻¹' S) := measurable_sigma_map_id hGm hS
  rw [← (h.hasLaw_stoppedValue_sigmaHistory hSG).map_eq,
    ← (h'.hasLaw_stoppedValue_sigmaHistory hS).map_eq,
    Measure.map_map (measurable_sigma_map_id hGm)
      (measurable_stoppedValue_sigmaHistory h.measurable_obs h.measurable_action
        h.measurable_feedback (measurable_hittingAfter_sigmaHistory h.measurable_obs
          h.measurable_action h.measurable_feedback hSG))]
  congr 1
  funext ω
  rw [Function.comp_apply, sigmaMap_stoppedValue_sigmaHistory G hG,
    hittingAfter_sigmaHistory_preimage G hG]

end Stopped

/-! ### Partial feedback -/

section PartialFeedback

variable {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {alg : Algorithm 𝓞 𝓐 𝓦} {env : Environment 𝓞 𝓐 𝓨} {env' : Environment 𝓞 𝓐 𝓦}
  {g : Round 𝓞 𝓐 𝓨 → 𝓦}

/-- **Runs with partial feedback.** Let `env` be an environment whose kernels read the past rounds
only through the partial feedback map `g`, and `env'` the corresponding environment on the partial
feedbacks: the observation kernels of `env` are those of `env'` on the histories seen through `g`,
and the law of `g (o, a, y)` under the feedback kernel of `env` is the feedback kernel of `env'`.
In a run of `alg.comapPartialFeedback g` in `env`, the observations, actions and partial
feedbacks form a run of `alg` in `env'`. -/
lemma IsAlgEnvSeq.partialFeedback (hg : Measurable g)
    (h_obs : ∀ n (h : Hist 𝓞 𝓐 𝓨 n), env.obs n h = env'.obs n (Hist.partialFeedback g h))
    (h_fb : ∀ n (h : Hist 𝓞 𝓐 𝓨 n) o a, (env.feedback n ((h, o), a)).map (fun y ↦ g (o, a, y)) =
      env'.feedback n ((Hist.partialFeedback g h, o), a))
    {P : Measure Ω} [IsFiniteMeasure P]
    (hseq : IsAlgEnvSeq O X Y (alg.comapPartialFeedback g hg) env P) :
    IsAlgEnvSeq O X (fun n ω ↦ g (O n ω, X n ω, Y n ω)) alg env' P where
  measurable_obs := hseq.measurable_obs
  measurable_action := hseq.measurable_action
  measurable_feedback n := hg.comp ((hseq.measurable_obs n).prodMk
    ((hseq.measurable_action n).prodMk (hseq.measurable_feedback n)))
  hasCondDistrib_obs n := by
    have h_eq : env.obs n = (env'.obs n).comap (Hist.partialFeedback g)
        (Hist.measurable_partialFeedback hg n) := by
      ext h : 1
      rw [Kernel.comap_apply, h_obs]
    have h1 := hseq.hasCondDistrib_obs n
    rw [h_eq] at h1
    exact h1.comp_right
  hasCondDistrib_action n := hseq.hasCondDistrib_action_comapPartialFeedback n
  hasCondDistrib_feedback n := by
    have h1 := (hseq.hasCondDistrib_feedback n).map_of_forall_eq
      (F := fun (p : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) y ↦ g (p.1.2, p.2, y))
      (η := (env'.feedback n).comap
        (fun p : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 ↦ ((Hist.partialFeedback g p.1.1, p.1.2), p.2))
        (by fun_prop))
      (hg.comp (by fun_prop)) (fun p ↦ by rw [Kernel.comap_apply, ← h_fb])
    exact h1.comp_right

/-- **Output law with partial feedback.** If the kernels of `env` read the past rounds only
through the partial feedback map `g`, and `env'` is the corresponding environment on the partial
feedbacks, the output of `A.comapPartialFeedback g` in `env` has the law of the output of `A` in
`env'`. -/
lemma IdentAlg.outputMeasure_comapPartialFeedback (A : IdentAlg 𝓞 𝓐 𝓦 𝓩) (hg : Measurable g)
    (h_obs : ∀ n (h : Hist 𝓞 𝓐 𝓨 n), env.obs n h = env'.obs n (Hist.partialFeedback g h))
    (h_fb : ∀ n (h : Hist 𝓞 𝓐 𝓨 n) o a, (env.feedback n ((h, o), a)).map (fun y ↦ g (o, a, y)) =
      env'.feedback n ((Hist.partialFeedback g h, o), a)) :
    (A.comapPartialFeedback g hg).outputMeasure env = A.outputMeasure env' := by
  have hseq := IT.isAlgEnvSeq_trajMeasure (A.comapPartialFeedback g hg).alg env
  have h' := hseq.partialFeedback (alg := A.alg) hg h_obs h_fb
  have hG : ∀ n, Measurable (Hist.partialFeedback g (n := n)) :=
    Hist.measurable_partialFeedback hg
  rw [IdentAlg.outputMeasure, IdentAlg.outputMeasure, ← map_stoppedHistMeasure_of_history_eq hseq h'
    (fun _ ↦ Hist.partialFeedback g) hG (fun _ _ ↦ rfl) A.measurableSet_stopSet,
    ← Measure.comap_comp _ (measurable_sigma_map_id hG)]
  rfl

end PartialFeedback

/-! ### Relabelling along maps of the observations and the feedbacks -/

section ObsFeedback

variable {fo : 𝓞' → 𝓞} {fy : 𝓨' → 𝓨}

/-- The identification algorithm on `𝓞'`, `𝓨'` obtained from `A` by reading the observations
through `fo` and the feedbacks through `fy`: its sampling, stopping and output rules apply those of
`A` to the transported histories. -/
noncomputable def IdentAlg.comapObsFeedback (A : IdentAlg 𝓞 𝓐 𝓨 𝓩) (fo : 𝓞' → 𝓞) (fy : 𝓨' → 𝓨)
    (hfo : Measurable fo) (hfy : Measurable fy) : IdentAlg 𝓞' 𝓐 𝓨' 𝓩 where
  alg := A.alg.comap (fun _ p ↦ (Hist.map fo id fy p.1, fo p.2)) fun _ ↦ by fun_prop
  stopSet := Sigma.map id (fun _ ↦ Hist.map fo id fy) ⁻¹' A.stopSet
  measurableSet_stopSet := measurable_sigma_map_id (fun _ ↦ by fun_prop) A.measurableSet_stopSet
  output := A.output.comap (Sigma.map id fun _ ↦ Hist.map fo id fy)
    (measurable_sigma_map_id fun _ ↦ by fun_prop)

/-- **Relabelling of runs.** If the kernels of `env` on the histories transported by `fo` and `fy`
are the images by `fo` and `fy` of the kernels of `env'`, then a run in `env'` of the algorithm
reading its rounds through `fo` and `fy`, transported by `fo` and `fy`, is a run of `alg` in
`env`. -/
lemma IsAlgEnvSeq.mapObsFeedback {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    {env' : Environment 𝓞' 𝓐 𝓨'} (hfo : Measurable fo) (hfy : Measurable fy)
    (h_obs : ∀ n (h : Hist 𝓞' 𝓐 𝓨' n), env.obs n (Hist.map fo id fy h) = (env'.obs n h).map fo)
    (h_fb : ∀ n (h : Hist 𝓞' 𝓐 𝓨' n) o a, env.feedback n ((Hist.map fo id fy h, fo o), a) =
      (env'.feedback n ((h, o), a)).map fy)
    {O' : ℕ → Ω → 𝓞'} {X : ℕ → Ω → 𝓐} {Y' : ℕ → Ω → 𝓨'} {P : Measure Ω} [IsFiniteMeasure P]
    (hseq : IsAlgEnvSeq O' X Y'
      (alg.comap (fun _ p ↦ (Hist.map fo id fy p.1, fo p.2)) fun _ ↦ by fun_prop) env' P) :
    IsAlgEnvSeq (fun n ω ↦ fo (O' n ω)) X (fun n ω ↦ fy (Y' n ω)) alg env P where
  measurable_obs n := hfo.comp (hseq.measurable_obs n)
  measurable_action := hseq.measurable_action
  measurable_feedback n := hfy.comp (hseq.measurable_feedback n)
  hasCondDistrib_obs n := by
    have h_eq : (env'.obs n).map fo = (env.obs n).comap (Hist.map fo id fy) (by fun_prop) := by
      ext h : 1
      rw [Kernel.map_apply _ hfo, Kernel.comap_apply, h_obs]
    have h1 := (hseq.hasCondDistrib_obs n).comp_left hfo
    rw [h_eq] at h1
    exact h1.comp_right
  hasCondDistrib_action n := (hseq.hasCondDistrib_action n).comp_right (hf := by fun_prop)
  hasCondDistrib_feedback n := by
    have h_eq : (env'.feedback n).map fy = (env.feedback n).comap
        (fun p : (Hist 𝓞' 𝓐 𝓨' n × 𝓞') × 𝓐 ↦ ((Hist.map fo id fy p.1.1, fo p.1.2), p.2))
        (by fun_prop) := by
      ext p : 1
      rw [Kernel.map_apply _ hfy, Kernel.comap_apply, h_fb]
    have h1 := (hseq.hasCondDistrib_feedback n).comp_left hfy
    rw [h_eq] at h1
    exact h1.comp_right

/-- **Output law of a relabelled algorithm.** If the kernels of `env` on the histories transported
by `fo` and `fy` are the images by `fo` and `fy` of the kernels of `env'`, the output of `A` in
`env` has the law of the output of `A.comapObsFeedback fo fy` in `env'`. -/
lemma IdentAlg.outputMeasure_comapObsFeedback (A : IdentAlg 𝓞 𝓐 𝓨 𝓩) (hfo : Measurable fo)
    (hfy : Measurable fy) {env : Environment 𝓞 𝓐 𝓨} {env' : Environment 𝓞' 𝓐 𝓨'}
    (h_obs : ∀ n (h : Hist 𝓞' 𝓐 𝓨' n), env.obs n (Hist.map fo id fy h) = (env'.obs n h).map fo)
    (h_fb : ∀ n (h : Hist 𝓞' 𝓐 𝓨' n) o a, env.feedback n ((Hist.map fo id fy h, fo o), a) =
      (env'.feedback n ((h, o), a)).map fy) :
    (A.comapObsFeedback fo fy hfo hfy).outputMeasure env' = A.outputMeasure env := by
  have hseq := IT.isAlgEnvSeq_trajMeasure (A.comapObsFeedback fo fy hfo hfy).alg env'
  have h' := hseq.mapObsFeedback (alg := A.alg) hfo hfy h_obs h_fb
  have hG : ∀ n, Measurable (Hist.map fo (id : 𝓐 → 𝓐) fy (n := n)) := fun _ ↦ by fun_prop
  rw [IdentAlg.outputMeasure, IdentAlg.outputMeasure, ← map_stoppedHistMeasure_of_history_eq hseq h'
    (fun _ ↦ Hist.map fo id fy) hG (fun _ _ ↦ rfl) A.measurableSet_stopSet,
    ← Measure.comap_comp _ (measurable_sigma_map_id hG)]
  rfl

end ObsFeedback

end Learning
