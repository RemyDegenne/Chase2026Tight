/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IdentificationAlg
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.FactorsThrough

/-!
# Partial feedback: algorithms observing a function of each round

An algorithm `alg` with feedback in `𝓦` can be run in a setting where the feedback of a round is
an element `y : 𝓨` of which only `g (o, a, y) : 𝓦` is observed (a function of the observation,
the action and the feedback of the round, e.g. the loss of the pulled arm when `y` is a loss
vector): `alg.comapPartialFeedback g` is the algorithm with feedback in `𝓨` that applies the
policy of `alg` to the history seen through `g` (`Hist.partialFeedback g`). This is the transport
of `alg` along a round-wise history map (LML's `Algorithm.comap`); LML's `Algorithm.comapFeedback`
is the case where `g` reads only the feedback (`Algorithm.comapPartialFeedback_feedback`).

The same transport applies to LML's identification algorithms (`IdentAlg.comap`,
`IdentAlg.comapPartialFeedback`): the sampling rule, stopping rule and output rule all see the
history through the history maps.

## Main definitions

* `Round.partialFeedback g r`, `Hist.partialFeedback g h`: a round (a history) in which the
  feedback of each round `r` is replaced by `g r`.
* `Algorithm.comapPartialFeedback alg g`: the algorithm seeing the feedback `g r` of each round.
* `IdentAlg.comap A F hF G hG`, `IdentAlg.comapPartialFeedback A g`: the same transports for
  identification algorithms.

## Main statements

* `IsAlgEnvSeq.hasCondDistrib_action_comapPartialFeedback`: in a run of
  `alg.comapPartialFeedback g`, the action of round `n` has conditional distribution
  `alg.policy n` given the history seen through `g` and the observation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 𝓦 𝓩 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓦 : MeasurableSpace 𝓦} {m𝓩 : MeasurableSpace 𝓩}

/-! ### Rounds and histories seen through a partial feedback map -/

/-- The round `r = (o, a, y)` in which the feedback is replaced by the partial feedback `g r`, a
function of the whole round: `(o, a, g (o, a, y))`. -/
def Round.partialFeedback (g : Round 𝓞 𝓐 𝓨 → 𝓦) (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 𝓐 𝓦 :=
  (r.obs, r.action, g r)

@[simp]
lemma Round.obs_partialFeedback (g : Round 𝓞 𝓐 𝓨 → 𝓦) (r : Round 𝓞 𝓐 𝓨) :
    (Round.partialFeedback g r).obs = r.obs := rfl

@[simp]
lemma Round.action_partialFeedback (g : Round 𝓞 𝓐 𝓨 → 𝓦) (r : Round 𝓞 𝓐 𝓨) :
    (Round.partialFeedback g r).action = r.action := rfl

@[simp]
lemma Round.feedback_partialFeedback (g : Round 𝓞 𝓐 𝓨 → 𝓦) (r : Round 𝓞 𝓐 𝓨) :
    (Round.partialFeedback g r).feedback = g r := rfl

/-- A partial feedback map reading only the feedback gives LML's `Round.mapFeedback`. -/
lemma Round.partialFeedback_feedback (f : 𝓨 → 𝓦) :
    Round.partialFeedback (fun r : Round 𝓞 𝓐 𝓨 ↦ f r.feedback) = Round.mapFeedback f := rfl

@[fun_prop]
lemma Round.measurable_partialFeedback {g : Round 𝓞 𝓐 𝓨 → 𝓦} (hg : Measurable g) :
    Measurable (Round.partialFeedback g) :=
  Round.measurable_obs.prodMk (Round.measurable_action.prodMk hg)

/-- A history seen through the partial feedback map `g`: the feedback of each round `r` is
replaced by `g r`. -/
def Hist.partialFeedback (g : Round 𝓞 𝓐 𝓨 → 𝓦) {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞 𝓐 𝓦 n :=
  fun i ↦ Round.partialFeedback g (h i)

@[simp]
lemma Hist.partialFeedback_apply (g : Round 𝓞 𝓐 𝓨 → 𝓦) {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) (i : Fin n) :
    Hist.partialFeedback g h i = Round.partialFeedback g (h i) := rfl

/-- A partial feedback map reading only the feedback gives LML's `Hist.mapFeedback`. -/
lemma Hist.partialFeedback_feedback (f : 𝓨 → 𝓦) (n : ℕ) :
    Hist.partialFeedback (fun r : Round 𝓞 𝓐 𝓨 ↦ f r.feedback) (n := n) = Hist.mapFeedback f :=
  rfl

@[fun_prop]
lemma Hist.measurable_partialFeedback {g : Round 𝓞 𝓐 𝓨 → 𝓦} (hg : Measurable g) (n : ℕ) :
    Measurable (Hist.partialFeedback g (n := n)) :=
  Measurable.of_eval fun i ↦ (Round.measurable_partialFeedback hg).comp (measurable_pi_apply i)

/-! ### Algorithms -/

/-- The algorithm with feedback in `𝓨` obtained from an algorithm `alg` with feedback in `𝓦` by
observing `g (o, a, y)` of each round `(o, a, y)` of the history: the transport of `alg` along
the round-wise history map `Hist.partialFeedback g`. -/
noncomputable def Algorithm.comapPartialFeedback (alg : Algorithm 𝓞 𝓐 𝓦)
    (g : Round 𝓞 𝓐 𝓨 → 𝓦) (hg : Measurable g := by fun_prop) : Algorithm 𝓞 𝓐 𝓨 :=
  alg.comap (fun _ p ↦ (Hist.partialFeedback g p.1, p.2))
    fun n ↦ ((Hist.measurable_partialFeedback hg n).comp measurable_fst).prodMk measurable_snd

@[simp]
lemma Algorithm.policy_comapPartialFeedback (alg : Algorithm 𝓞 𝓐 𝓦) (g : Round 𝓞 𝓐 𝓨 → 𝓦)
    (hg : Measurable g) (n : ℕ) :
    (alg.comapPartialFeedback g hg).policy n =
      (alg.policy n).comap (fun p ↦ (Hist.partialFeedback g p.1, p.2))
        (((Hist.measurable_partialFeedback hg n).comp measurable_fst).prodMk measurable_snd) :=
  rfl

/-- A partial feedback map reading only the feedback gives LML's `Algorithm.comapFeedback`. -/
lemma Algorithm.comapPartialFeedback_feedback (alg : Algorithm 𝓞 𝓐 𝓦) {f : 𝓨 → 𝓦}
    (hf : Measurable f) :
    alg.comapPartialFeedback (fun r ↦ f r.feedback) (hf.comp Round.measurable_feedback)
      = alg.comapFeedback f hf := rfl

/-- `alg.comapPartialFeedback g` factors through the history seen through `g` and the
observation. -/
lemma Algorithm.factorsThrough_comapPartialFeedback (alg : Algorithm 𝓞 𝓐 𝓦)
    (g : Round 𝓞 𝓐 𝓨 → 𝓦) (hg : Measurable g) :
    (alg.comapPartialFeedback g hg).FactorsThrough fun _ p ↦ (Hist.partialFeedback g p.1, p.2) :=
  alg.factorsThrough_comap _ _

/-! ### Identification algorithms -/

/-- The map `⟨i, x⟩ ↦ ⟨i, G i x⟩` between sigma types is measurable if all the maps `G i` are. -/
lemma measurable_sigma_map_id {ι : Type*} {β γ : ι → Type*} [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSpace (γ i)] {G : ∀ i, β i → γ i} (hG : ∀ i, Measurable (G i)) :
    Measurable (Sigma.map id G : (Σ i, β i) → Σ i, γ i) :=
  measurable_sigma_of_measurable_comp_mk fun i ↦ (measurable_sigma_mk i).comp (hG i)

/-- The identification algorithm with feedback in `𝓨` obtained from `A` with feedback in `𝓦` by
transforming the histories: the sampling rule uses the history maps `F n` on pairs (history,
current observation), the stopping and output rules the history maps `G n` on histories of `n`
rounds. -/
noncomputable def IdentAlg.comap (A : IdentAlg 𝓞 𝓐 𝓦 𝓩)
    (F : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → Hist 𝓞 𝓐 𝓦 n × 𝓞) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Hist 𝓞 𝓐 𝓦 n) (hG : ∀ n, Measurable (G n)) :
    IdentAlg 𝓞 𝓐 𝓨 𝓩 where
  alg := A.alg.comap F hF
  stopSet := Sigma.map id G ⁻¹' A.stopSet
  measurableSet_stopSet := measurable_sigma_map_id hG A.measurableSet_stopSet
  output := A.output.comap (Sigma.map id G) (measurable_sigma_map_id hG)

section IdentAlgComap

variable (A : IdentAlg 𝓞 𝓐 𝓦 𝓩) {F : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → Hist 𝓞 𝓐 𝓦 n × 𝓞}
  (hF : ∀ n, Measurable (F n)) {G : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Hist 𝓞 𝓐 𝓦 n}
  (hG : ∀ n, Measurable (G n))

@[simp]
lemma IdentAlg.comap_alg : (A.comap F hF G hG).alg = A.alg.comap F hF := rfl

@[simp]
lemma IdentAlg.mem_stopSet_comap (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) :
    ⟨n, h⟩ ∈ (A.comap F hF G hG).stopSet ↔ ⟨n, G n h⟩ ∈ A.stopSet := Iff.rfl

@[simp]
lemma IdentAlg.comap_output_mk (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) :
    (A.comap F hF G hG).output ⟨n, h⟩ = A.output ⟨n, G n h⟩ := rfl

end IdentAlgComap

/-- The identification algorithm with feedback in `𝓨` obtained from `A` with feedback in `𝓦` by
observing `g (o, a, y)` of each round: sampling, stopping and output rules all see the history
through `g`. -/
noncomputable def IdentAlg.comapPartialFeedback (A : IdentAlg 𝓞 𝓐 𝓦 𝓩)
    (g : Round 𝓞 𝓐 𝓨 → 𝓦) (hg : Measurable g := by fun_prop) : IdentAlg 𝓞 𝓐 𝓨 𝓩 :=
  A.comap (fun _ p ↦ (Hist.partialFeedback g p.1, p.2))
    (fun n ↦ ((Hist.measurable_partialFeedback hg n).comp measurable_fst).prodMk measurable_snd)
    (fun _ ↦ Hist.partialFeedback g) fun n ↦ Hist.measurable_partialFeedback hg n

@[simp]
lemma IdentAlg.comapPartialFeedback_alg (A : IdentAlg 𝓞 𝓐 𝓦 𝓩) (g : Round 𝓞 𝓐 𝓨 → 𝓦)
    (hg : Measurable g) :
    (A.comapPartialFeedback g hg).alg = A.alg.comapPartialFeedback g hg := rfl

@[simp]
lemma IdentAlg.mem_stopSet_comapPartialFeedback (A : IdentAlg 𝓞 𝓐 𝓦 𝓩)
    (g : Round 𝓞 𝓐 𝓨 → 𝓦) (hg : Measurable g) (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) :
    ⟨n, h⟩ ∈ (A.comapPartialFeedback g hg).stopSet ↔ ⟨n, Hist.partialFeedback g h⟩ ∈ A.stopSet :=
  Iff.rfl

@[simp]
lemma IdentAlg.comapPartialFeedback_output_mk (A : IdentAlg 𝓞 𝓐 𝓦 𝓩)
    (g : Round 𝓞 𝓐 𝓨 → 𝓦) (hg : Measurable g) (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) :
    (A.comapPartialFeedback g hg).output ⟨n, h⟩ = A.output ⟨n, Hist.partialFeedback g h⟩ := rfl

/-! ### Runs -/

/-- **Runs of `comapPartialFeedback`.** In a run of `alg.comapPartialFeedback g` against any
environment, the action of round `n` has conditional distribution `alg.policy n` given the
history seen through `g` and the observation of round `n`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_comapPartialFeedback {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {alg : Algorithm 𝓞 𝓐 𝓦} {env : Environment 𝓞 𝓐 𝓨}
    {g : Round 𝓞 𝓐 𝓨 → 𝓦} {hg : Measurable g} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐}
    {Y : ℕ → Ω → 𝓨} (h : IsAlgEnvSeq O A Y (alg.comapPartialFeedback g hg) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (history O A (fun n ω ↦ g (O n ω, A n ω, Y n ω)) n ω, O n ω)) (alg.policy n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞 𝓐 𝓨 n × 𝓞 ↦ (Hist.partialFeedback g p.1, p.2))
    (hf := ((Hist.measurable_partialFeedback hg n).comp measurable_fst).prodMk measurable_snd)
    (h.hasCondDistrib_action n)

end Learning
