/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Chase2026Tight.LeanMachineLearning.Online.Convex.Regret
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.ObliviousEnv
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.PartialFeedback
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Adversarial bandits

The *adversarial* (non-stochastic) bandit with arms `α`: at each round `t` the adversary sets a
loss vector `ℓ_t : α → ℝ` while the learner pulls an arm `a_t`, and the learner observes only the
loss `ℓ_t a_t` of the arm it pulled (*bandit feedback*). The adversary may be *adaptive*: the loss
vector of a round may depend on the past rounds (arms pulled and losses), but not on the arm
pulled in that round.

## Modelling

A round is a `Round 𝓞 α (α → ℝ)`: an observation (`Unit` for the `K`-armed bandit, the advice
of the experts for the bandit with expert advice of `Online/Bandit/ExpertAdvice.lean`), the arm
pulled as action and the loss vector as feedback.

* An adversary is an `Environment 𝓞 α (α → ℝ)` whose feedback kernels ignore the current action
  (`Environment.FeedbackIgnoresAction` of `SequentialLearning/ObliviousEnv.lean`). Its losses
  lie in `[0, 1]` if `env.FeedbackIn (Set.Icc 0 1)` (with Mathlib's order on `α → ℝ`), and in a
  set `s` if `env.FeedbackIn (Set.univ.pi fun _ ↦ s)`. The oblivious adversaries are the
  environments `Environment.ofSeq ℓ` (committed loss sequence) and `Environment.const` (stochastic
  losses).
* A learner is an algorithm with real feedback, `alg : Algorithm 𝓞 α ℝ`: it sees the loss of the
  arm it pulled. `alg.comapBanditFeedback : Algorithm 𝓞 α (α → ℝ)` is the same learner run
  against loss vectors, of which it sees only `banditFeedback r = r.feedback r.action`
  (`Algorithm.comapPartialFeedback`). Learners with their own randomness that they must remember
  (a number of resampling steps, a sampled perturbation) *announce* it: they play in `𝓩 × α`
  against `env.comapAction Prod.snd` and `alg.comapBanditFeedbackAnn` sees the loss
  `banditFeedbackAnn r = r.feedback r.action.2` of the arm.

## Main definitions

* `banditFeedback`, `banditFeedbackAnn`: the loss of the pulled arm in a round;
* `Algorithm.comapBanditFeedback`, `Algorithm.comapBanditFeedbackAnn`,
  `IdentAlg.comapBanditFeedback`: learners with bandit feedback run against loss vectors;
* `pseudoRegret P A Y T = max_i E[∑_{t < T} (Y t (A t) - Y t i)]`: the pseudo-regret after `T`
  rounds of a run with arms `A` and loss vectors `Y`, the largest expected regret `ocoRegret`
  (`Online/Convex/Regret.lean`) of the run against a fixed arm;
* `IsSelfBounding R P I Δ C T`: the *adversarial regime with a `(Δ, C, T)` self-bounding
  constraint* (Zimmert, Seldin 2021) for a run whose regret is `R` and whose sequence of chosen
  indices (arms, or experts) is `I`: `R ≥ E[∑_{t < T} Δ (I t)] - C`. This covers the stochastic
  regime (`C = 0`, `Δ` the suboptimality gaps) and stochastic losses with adversarial
  corruptions of total amount `C`.

## Main results

* `IsAlgEnvSeq.hasCondDistrib_action_comapBanditFeedback`: in a run of `alg.comapBanditFeedback`,
  the arm of round `n` has conditional distribution `alg.policy n` given the history with bandit
  feedback and the observation of round `n`;
* `pseudoRegret_eq_iSup_integral_sum_sub`: the explicit form of the pseudo-regret;
* `pseudoRegret_eq_of_isAlgEnvSeq_ofSeq`: against the oblivious adversary `Environment.ofSeq ℓ`, the
  pseudo-regret is the largest expected regret for the fixed loss vectors `ℓ`;
* `iSup_ocoRegret_eq_expertRegret`: the regret against the best arm in hindsight is the expert
  regret `expertRegret` of the Dirac weights of the arms pulled;
* `pseudoRegret_le_integral_expertRegret`: the pseudo-regret is at most the expected regret
  against the best arm in hindsight.

The `K`-armed bandit is also the special case of the bandit with expert advice in which the
experts are the arms (`pseudoRegret_eq_expertPseudoRegret`, `Online/Bandit/ExpertAdvice.lean`)
and of the adversarial linear bandit with the basis vectors as actions
(`pseudoRegret_eq_iSup_integral_linRegret`, `Online/Bandit/AdversarialLinear.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

namespace Bandits

variable {𝓞 α 𝓨 𝓩 : Type*} {m𝓞 : MeasurableSpace 𝓞} {mα : MeasurableSpace α}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}

/-! ### Bandit feedback -/

/-- The *bandit feedback* of a round whose feedback is a loss vector: the loss of the pulled
arm. -/
def banditFeedback (r : Round 𝓞 α (α → 𝓨)) : 𝓨 := r.feedback r.action

@[simp]
lemma banditFeedback_mk (o : 𝓞) (a : α) (ℓ : α → 𝓨) : banditFeedback (o, a, ℓ) = ℓ a := rfl

/-- The bandit feedback of a round of an announcing learner, which plays `(z, a)` with announced
`z`: the loss of the pulled arm `a`. -/
def banditFeedbackAnn (r : Round 𝓞 (𝓩 × α) (α → 𝓨)) : 𝓨 := r.feedback r.action.2

@[simp]
lemma banditFeedbackAnn_mk (o : 𝓞) (z : 𝓩) (a : α) (ℓ : α → 𝓨) :
    banditFeedbackAnn (o, (z, a), ℓ) = ℓ a := rfl

/-- The bandit feedback of an announcing learner is the bandit feedback of the round in which the
announced variable is forgotten. -/
lemma banditFeedbackAnn_eq_banditFeedback (r : Round 𝓞 (𝓩 × α) (α → 𝓨)) :
    banditFeedbackAnn r = banditFeedback (Round.mapAction Prod.snd r) := rfl

section Measurability

variable [Countable α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_banditFeedback : Measurable (banditFeedback (𝓞 := 𝓞) (α := α) (𝓨 := 𝓨)) :=
  measurable_eval_prod.comp (Round.measurable_feedback.prodMk Round.measurable_action)

@[fun_prop]
lemma measurable_banditFeedbackAnn :
    Measurable (banditFeedbackAnn (𝓞 := 𝓞) (α := α) (𝓨 := 𝓨) (𝓩 := 𝓩)) :=
  measurable_eval_prod.comp
    (Round.measurable_feedback.prodMk (measurable_snd.comp Round.measurable_action))

end Measurability

end Bandits

/-! ### Learners with bandit feedback -/

namespace Learning

open Bandits

variable {𝓞 α 𝓨 𝓩 𝓩' : Type*} {m𝓞 : MeasurableSpace 𝓞} {mα : MeasurableSpace α}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩} {m𝓩' : MeasurableSpace 𝓩'}
  [Countable α] [MeasurableSingletonClass α]

/-- A learner with bandit feedback run against loss vectors: the algorithm with feedback the loss
vector of all arms, of which it sees only the loss of the arm it pulled. -/
noncomputable def Algorithm.comapBanditFeedback (alg : Algorithm 𝓞 α 𝓨) :
    Algorithm 𝓞 α (α → 𝓨) :=
  alg.comapPartialFeedback banditFeedback measurable_banditFeedback

@[simp]
lemma Algorithm.policy_comapBanditFeedback (alg : Algorithm 𝓞 α 𝓨) (n : ℕ) :
    alg.comapBanditFeedback.policy n =
      (alg.policy n).comap (fun p ↦ (Hist.partialFeedback banditFeedback p.1, p.2))
        (((Hist.measurable_partialFeedback measurable_banditFeedback n).comp
          measurable_fst).prodMk measurable_snd) :=
  rfl

/-- An announcing learner with bandit feedback (it plays `(z, a)` with announced `z`) run against
loss vectors: it sees only the loss of the arm `a` it pulled. -/
noncomputable def Algorithm.comapBanditFeedbackAnn (alg : Algorithm 𝓞 (𝓩 × α) 𝓨) :
    Algorithm 𝓞 (𝓩 × α) (α → 𝓨) :=
  alg.comapPartialFeedback banditFeedbackAnn measurable_banditFeedbackAnn

@[simp]
lemma Algorithm.policy_comapBanditFeedbackAnn (alg : Algorithm 𝓞 (𝓩 × α) 𝓨) (n : ℕ) :
    alg.comapBanditFeedbackAnn.policy n =
      (alg.policy n).comap (fun p ↦ (Hist.partialFeedback banditFeedbackAnn p.1, p.2))
        (((Hist.measurable_partialFeedback measurable_banditFeedbackAnn n).comp
          measurable_fst).prodMk measurable_snd) :=
  rfl

/-- An identification algorithm with bandit feedback run against loss vectors: its sampling,
stopping and output rules see only the losses of the pulled arms. -/
noncomputable def IdentAlg.comapBanditFeedback (A : IdentAlg 𝓞 α 𝓨 𝓩') :
    IdentAlg 𝓞 α (α → 𝓨) 𝓩' :=
  A.comapPartialFeedback banditFeedback measurable_banditFeedback

@[simp]
lemma IdentAlg.comapBanditFeedback_alg (A : IdentAlg 𝓞 α 𝓨 𝓩') :
    A.comapBanditFeedback.alg = A.alg.comapBanditFeedback := rfl

/-- **Runs of a learner with bandit feedback.** In a run of `alg.comapBanditFeedback` against any
environment, the arm of round `n` has conditional distribution `alg.policy n` given the history
with bandit feedback (the loss `Y t (A t)` of the pulled arm at each past round `t`) and the
observation of round `n`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_comapBanditFeedback {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {alg : Algorithm 𝓞 α 𝓨} {env : Environment 𝓞 α (α → 𝓨)}
    {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → α → 𝓨}
    (h : IsAlgEnvSeq O A Y alg.comapBanditFeedback env P) (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (history O A (fun n ω ↦ Y n ω (A n ω)) n ω, O n ω))
      (alg.policy n) P :=
  h.hasCondDistrib_action_comapPartialFeedback n

/-- **Runs of an announcing learner with bandit feedback.** In a run of
`alg.comapBanditFeedbackAnn`, the action of round `n` has conditional distribution
`alg.policy n` given the history with bandit feedback and the observation of round `n`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_comapBanditFeedbackAnn {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {alg : Algorithm 𝓞 (𝓩 × α) 𝓨}
    {env : Environment 𝓞 (𝓩 × α) (α → 𝓨)} {O : ℕ → Ω → 𝓞} {B : ℕ → Ω → 𝓩 × α}
    {Y : ℕ → Ω → α → 𝓨} (h : IsAlgEnvSeq O B Y alg.comapBanditFeedbackAnn env P) (n : ℕ) :
    HasCondDistrib (B n) (fun ω ↦ (history O B (fun n ω ↦ Y n ω (B n ω).2) n ω, O n ω))
      (alg.policy n) P :=
  h.hasCondDistrib_action_comapPartialFeedback n

end Learning

/-! ### Pseudo-regret -/

namespace Bandits

variable {α ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The pseudo-regret after `T` rounds of a run with arms `A` and loss vectors `Y`:
`max_i E[∑_{t < T} (Y t (A t) - Y t i)]`, the largest expected regret (`ocoRegret`) of the run
against a fixed arm. -/
noncomputable def pseudoRegret (P : Measure Ω) (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ) (T : ℕ) :
    ℝ :=
  ⨆ i, P[fun ω ↦ ocoRegret (fun t ↦ Y t ω) (fun t ↦ A t ω) T i]

lemma pseudoRegret_eq_iSup_integral_sum_sub (P : Measure Ω) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → α → ℝ) (T : ℕ) :
    pseudoRegret P A Y T = ⨆ i, P[fun ω ↦ ∑ t ∈ range T, (Y t ω (A t ω) - Y t ω i)] := by
  simp only [pseudoRegret, ocoRegret_eq_sum_sub]

@[simp]
lemma pseudoRegret_zero (P : Measure Ω) (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ) :
    pseudoRegret P A Y 0 = 0 := by
  simp [pseudoRegret]

/-- Against the oblivious adversary `Environment.ofSeq ℓ` committing to the loss vectors `ℓ`, the
pseudo-regret is the largest expected regret against a fixed arm for the loss vectors `ℓ`. -/
lemma pseudoRegret_eq_of_isAlgEnvSeq_ofSeq [Finite α] {mα : MeasurableSpace α}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {alg : Algorithm Unit α (α → ℝ)} {ℓ : ℕ → α → ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {Y : ℕ → Ω → α → ℝ} (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq ℓ) P) (T : ℕ) :
    pseudoRegret P A Y T = ⨆ i, P[fun ω ↦ ocoRegret ℓ (fun t ↦ A t ω) T i] := by
  have hY := feedback_ofSeq_ae_eq h
  refine congrArg iSup (funext fun i ↦ integral_congr_ae ?_)
  filter_upwards [hY] with ω hω
  simp only [show (fun t ↦ Y t ω) = ℓ from funext hω]

section Realized

variable [Fintype α] [DecidableEq α]

/-- The regret of the arms `a` against the arm `i` is the regret, for the linear losses
`p ↦ ∑_j p j * ℓ t j` of the experts problem, of the Dirac weights of the arms against the vertex
`i` of the simplex. -/
lemma ocoRegret_eq_ocoRegret_single (ℓ : ℕ → α → ℝ) (a : ℕ → α) (T : ℕ) (i : α) :
    ocoRegret ℓ a T i =
      ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) (fun t ↦ Pi.single (a t) 1) T (Pi.single i 1) := by
  rw [← ocoRegret_comp (fun t p ↦ ∑ j, p j * ℓ t j) (fun b ↦ (Pi.single b 1 : α → ℝ))]
  simp [Pi.single_apply]

/-- The regret of the arms `a` against the best arm in hindsight is the expert regret
`expertRegret` of the Dirac weights of the arms. -/
lemma iSup_ocoRegret_eq_expertRegret [Nonempty α] (ℓ : ℕ → α → ℝ) (a : ℕ → α) (T : ℕ) :
    ⨆ i, ocoRegret ℓ a T i = expertRegret ℓ (fun t ↦ Pi.single (a t) 1) T := by
  simp_rw [expertRegret_eq_iSup_ocoRegret, ocoRegret_eq_ocoRegret_single]

lemma ocoRegret_le_expertRegret (ℓ : ℕ → α → ℝ) (a : ℕ → α) (T : ℕ) (i : α) :
    ocoRegret ℓ a T i ≤ expertRegret ℓ (fun t ↦ Pi.single (a t) 1) T := by
  rw [ocoRegret_eq_ocoRegret_single]
  exact ocoRegret_single_le_expertRegret _ _ T i

/-- The pseudo-regret is at most the expected regret against the best arm in hindsight. -/
lemma pseudoRegret_le_integral_expertRegret [Nonempty α] {P : Measure Ω} {A : ℕ → Ω → α}
    {Y : ℕ → Ω → α → ℝ} {T : ℕ}
    (hint : ∀ i, Integrable (fun ω ↦ ocoRegret (fun t ↦ Y t ω) (fun t ↦ A t ω) T i) P)
    (hint' : Integrable (fun ω ↦ expertRegret (fun t ↦ Y t ω) (fun t ↦ Pi.single (A t ω) 1) T)
      P) :
    pseudoRegret P A Y T ≤
      P[fun ω ↦ expertRegret (fun t ↦ Y t ω) (fun t ↦ Pi.single (A t ω) 1) T] :=
  ciSup_le fun i ↦ integral_mono (hint i) hint' fun _ ↦ ocoRegret_le_expertRegret _ _ T i

end Realized

/-! ### Self-bounding regime -/

/-- The *adversarial regime with a `(Δ, C, T)` self-bounding constraint* (Zimmert, Seldin 2021),
for a run whose regret after `T` rounds is `R` and whose chosen indices are `I`: the regret is at
least `E[∑_{t < T} Δ (I t)] - C`. -/
def IsSelfBounding (R : ℝ) (P : Measure Ω) (I : ℕ → Ω → ι) (Δ : ι → ℝ) (C : ℝ) (T : ℕ) :
    Prop :=
  P[fun ω ↦ ∑ t ∈ range T, Δ (I t ω)] - C ≤ R

lemma IsSelfBounding.mono {R R' : ℝ} {P : Measure Ω} {I : ℕ → Ω → ι} {Δ : ι → ℝ} {C : ℝ} {T : ℕ}
    (h : IsSelfBounding R P I Δ C T) (hR : R ≤ R') : IsSelfBounding R' P I Δ C T :=
  h.trans hR

end Bandits
