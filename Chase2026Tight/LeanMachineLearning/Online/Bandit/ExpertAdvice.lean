/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.Mathlib.Analysis.Convex.Simplex
public import Chase2026Tight.LeanMachineLearning.Online.Bandit.Adversarial

/-!
# Bandits with expert advice

The *bandit with expert advice* problem (EXP4, Auer, Cesa-Bianchi, Freund, Schapire 2002), also
called the contextual bandit problem, with arms `α` and experts `ι`: at each round `t`, each
expert `j` gives an *advice vector* `π_t j`, a probability vector over the arms, which is shown to
the learner; the learner then pulls an arm `a_t` while the adversary sets the losses
`ℓ_t : α → ℝ` of all arms; the learner observes only `ℓ_t a_t`. The loss of expert `j` at round
`t` is its expected loss `∑_a π_t j a ℓ_t a` (`expertLoss`). The adversary is adaptive: the advice
and the losses of a round may depend on the past rounds.

*Deterministic advice*, in which each expert names an arm `e_t j : α`, is the special case of the
Dirac advice vectors `diracAdvice e` (`expertLoss_diracAdvice`), and the `K`-armed adversarial
bandit of `Online/Bandit/Adversarial.lean` is the case of the experts `α` each always advising
its own arm (`pseudoRegret_eq_expertPseudoRegret`).

## Modelling

A round is a `Round 𝓞 α (α → ℝ)` (`Online/Bandit/Adversarial.lean`) with the advice as
observation: `𝓞 = Advice ι α` for advice vectors, `𝓞 = ι → α` for deterministic advice.

* A learner is an `Algorithm 𝓞 α ℝ`, seeing the advice of the current round and, of each past
  round, the advice and the loss of the arm it pulled; it is run against loss vectors as
  `alg.comapBanditFeedback`. A learner for advice vectors is a learner for deterministic advice
  through LML's `Algorithm.comapObs` along `diracAdvice` (`measurable_diracAdvice`).
* An adversary is an environment `Environment 𝓞 α (α → ℝ)` whose feedback ignores the action of the
  current round (`Environment.FeedbackIgnoresAction`); its advice lies in a set `s` if `env.ObsIn s`
  (`SequentialLearning/ObliviousEnv.lean`), its losses in `[0, 1]` if
  `env.FeedbackIn (Set.Icc 0 1)`.

## Main definitions

* `Advice ι α = ι → simplex α`, `diracAdvice e`: advice vectors, and deterministic advice as
  Dirac advice vectors;
* `expertLoss π ℓ j = ∑_a π j a ℓ a`: the loss of expert `j`;
* `AdviceBoundedBelow ν π`: all advice probabilities lie in `[ν, 1] ∪ {0}`;
* `adviceRegret π a ℓ T j`: the regret of the arms `a` against the expert `j` over `T` rounds;
* `expertPseudoRegret P O A Y T = max_j E[adviceRegret (O · ω) (A · ω) (Y · ω) T j]`: the
  pseudo-regret of a run with advice `O`, arms `A` and loss vectors `Y`.

## Main results

* `expertLoss_diracAdvice`, `adviceRegret_diracAdvice`, `expertPseudoRegret_diracAdvice`:
  deterministic advice;
* `adviceRegret_const_diracAdvice_id`, `pseudoRegret_eq_expertPseudoRegret`: the `K`-armed bandit
  is the bandit with the experts `α` each advising its own arm;
* `iSup_adviceRegret_eq_sub_iInf`, `expertPseudoRegret_le_integral_iSup_adviceRegret`: regret
  against the best expert in hindsight, and the pseudo-regret is at most its expectation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

namespace Bandits

variable {α ι Ω : Type*} [Fintype α]

/-! ### Advice -/

/-- The advice of the experts `ι`: a probability vector over the arms `α` for each expert. -/
abbrev Advice (ι α : Type*) [Fintype α] := ι → simplex α

/-- Deterministic advice `e : ι → α` (expert `j` names the arm `e j`) as Dirac advice vectors. -/
noncomputable def diracAdvice [DecidableEq α] (e : ι → α) : Advice ι α :=
  fun j ↦ ⟨EuclideanSpace.single (e j) 1, single_mem_simplex (e j)⟩

@[simp]
lemma coe_diracAdvice [DecidableEq α] (e : ι → α) (j : ι) :
    (diracAdvice e j : α → ℝ) = Pi.single (e j) 1 := rfl

/-- The loss `∑_a π j a ℓ a` of expert `j` under the advice `π` and the loss vector `ℓ`: the
expected loss of an arm drawn from its advice vector. -/
def expertLoss (π : Advice ι α) (ℓ : α → ℝ) (j : ι) : ℝ := ∑ a, π j a * ℓ a

/-- The loss of an expert with deterministic advice is the loss of the arm it names. -/
@[simp]
lemma expertLoss_diracAdvice [DecidableEq α] (e : ι → α) (ℓ : α → ℝ) (j : ι) :
    expertLoss (diracAdvice e) ℓ j = ℓ (e j) := by
  simp [expertLoss, Pi.single_apply]

/-- All the advice probabilities lie in `[ν, 1] ∪ {0}`: an arm advised with positive probability
is advised with probability at least `ν`. -/
def AdviceBoundedBelow (ν : ℝ) (π : Advice ι α) : Prop :=
  ∀ i a, π i a ∈ Set.Icc ν 1 ∪ {0}

/-- Deterministic advice satisfies `AdviceBoundedBelow ν` for every `ν ≤ 1`. -/
lemma adviceBoundedBelow_diracAdvice [DecidableEq α] {ν : ℝ} (hν : ν ≤ 1) (e : ι → α) :
    AdviceBoundedBelow ν (diracAdvice e) := by
  intro j a
  rcases eq_or_ne a (e j) with rfl | h
  · exact Or.inl (by simp [hν])
  · exact Or.inr (by simp [h])

section Measurability

variable {mα : MeasurableSpace α} [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_diracAdvice [DecidableEq α] : Measurable (diracAdvice (ι := ι) (α := α)) :=
  Measurable.of_eval fun j ↦ Measurable.subtype_mk
    ((measurable_of_countable fun a : α ↦ EuclideanSpace.single a (1 : ℝ)).comp
      (measurable_pi_apply j))

@[fun_prop]
lemma measurable_advice_apply [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    {X : Type*} [MeasurableSpace X] {π : X → Advice ι α} {j : X → ι} {a : X → α}
    (hπ : Measurable π) (hj : Measurable j) (ha : Measurable a) :
    Measurable fun x ↦ π x (j x) (a x) := by
  have h1 := measurable_eval_prod.comp (hπ.prodMk hj)
  have h2 := (WithLp.measurable_ofLp 2 _).comp (measurable_subtype_coe.comp h1)
  have h3 := measurable_eval_prod.comp (h2.prodMk ha)
  exact h3

end Measurability

@[fun_prop]
lemma measurable_expertLoss {X : Type*} [MeasurableSpace X] {π : X → Advice ι α}
    {ℓ : X → α → ℝ} (hπ : Measurable π) (hℓ : Measurable ℓ) (j : ι) :
    Measurable fun x ↦ expertLoss (π x) (ℓ x) j := by
  have h : Measurable fun x ↦ ⇑(π x j) :=
    measurable_coe_simplex.comp ((measurable_pi_apply j).comp hπ)
  exact Finset.measurable_sum _ fun a _ ↦
    ((measurable_pi_apply a).comp h).mul ((measurable_pi_apply a).comp hℓ)

/-! ### Regret -/

/-- The regret over `T` rounds of the arms `a` against the expert `j`, for the advice `π` and the
loss vectors `ℓ`: `∑_{t < T} ℓ t (a t) - ∑_{t < T} expertLoss (π t) (ℓ t) j`. -/
noncomputable def adviceRegret (π : ℕ → Advice ι α) (a : ℕ → α) (ℓ : ℕ → α → ℝ) (T : ℕ)
    (j : ι) : ℝ :=
  ∑ t ∈ range T, ℓ t (a t) - ∑ t ∈ range T, expertLoss (π t) (ℓ t) j

lemma adviceRegret_eq_sum_sub (π : ℕ → Advice ι α) (a : ℕ → α) (ℓ : ℕ → α → ℝ) (T : ℕ)
    (j : ι) :
    adviceRegret π a ℓ T j = ∑ t ∈ range T, (ℓ t (a t) - expertLoss (π t) (ℓ t) j) := by
  rw [adviceRegret, sum_sub_distrib]

@[simp]
lemma adviceRegret_zero (π : ℕ → Advice ι α) (a : ℕ → α) (ℓ : ℕ → α → ℝ) (j : ι) :
    adviceRegret π a ℓ 0 j = 0 := by
  simp [adviceRegret]

/-- The regret against an expert with deterministic advice `e`: the loss of the arms `a` minus
the loss of the arms `e t j` it names. -/
lemma adviceRegret_diracAdvice [DecidableEq α] (e : ℕ → ι → α) (a : ℕ → α) (ℓ : ℕ → α → ℝ)
    (T : ℕ) (j : ι) :
    adviceRegret (fun t ↦ diracAdvice (e t)) a ℓ T j =
      ∑ t ∈ range T, ℓ t (a t) - ∑ t ∈ range T, ℓ t (e t j) := by
  simp [adviceRegret]

/-- The regret against the expert `i` which always advises the arm `i` is the regret `ocoRegret`
against the arm `i`. -/
lemma adviceRegret_const_diracAdvice_id [DecidableEq α] (a : ℕ → α) (ℓ : ℕ → α → ℝ) (T : ℕ)
    (i : α) :
    adviceRegret (fun _ ↦ diracAdvice id) a ℓ T i = ocoRegret ℓ a T i := by
  simp [adviceRegret, ocoRegret]

/-- The regret against the best expert in hindsight. -/
lemma iSup_adviceRegret_eq_sub_iInf [Finite ι] [Nonempty ι] (π : ℕ → Advice ι α) (a : ℕ → α)
    (ℓ : ℕ → α → ℝ) (T : ℕ) :
    ⨆ j, adviceRegret π a ℓ T j =
      ∑ t ∈ range T, ℓ t (a t) - ⨅ j, ∑ t ∈ range T, expertLoss (π t) (ℓ t) j := by
  obtain ⟨j, hj⟩ := Finite.exists_min fun j : ι ↦ ∑ t ∈ range T, expertLoss (π t) (ℓ t) j
  have h : ⨅ j, ∑ t ∈ range T, expertLoss (π t) (ℓ t) j = ∑ t ∈ range T, expertLoss (π t) (ℓ t) j :=
    le_antisymm (ciInf_le (Set.finite_range _).bddBelow j) (le_ciInf hj)
  rw [h]
  exact le_antisymm (ciSup_le fun i ↦ sub_le_sub_left (hj i) _)
    (le_ciSup (f := fun i ↦ adviceRegret π a ℓ T i) (Set.finite_range _).bddAbove j)

variable {mΩ : MeasurableSpace Ω}

/-- The pseudo-regret after `T` rounds of a run with advice `O`, arms `A` and loss vectors `Y`:
`max_j E[∑_{t < T} (Y t (A t) - expertLoss (O t) (Y t) j)]`, the largest expected regret of the
run against an expert. -/
noncomputable def expertPseudoRegret (P : Measure Ω) (O : ℕ → Ω → Advice ι α) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → α → ℝ) (T : ℕ) : ℝ :=
  ⨆ j, P[fun ω ↦ adviceRegret (fun t ↦ O t ω) (fun t ↦ A t ω) (fun t ↦ Y t ω) T j]

lemma expertPseudoRegret_eq_iSup_integral_sum_sub (P : Measure Ω) (O : ℕ → Ω → Advice ι α)
    (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ) (T : ℕ) :
    expertPseudoRegret P O A Y T =
      ⨆ j, P[fun ω ↦ ∑ t ∈ range T, (Y t ω (A t ω) - expertLoss (O t ω) (Y t ω) j)] := by
  simp only [expertPseudoRegret, adviceRegret_eq_sum_sub]

/-- The pseudo-regret for deterministic advice `O`: the largest expected regret against the arms
named by an expert. -/
lemma expertPseudoRegret_diracAdvice [DecidableEq α] (P : Measure Ω) (O : ℕ → Ω → ι → α)
    (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ) (T : ℕ) :
    expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T =
      ⨆ j, P[fun ω ↦ ∑ t ∈ range T, (Y t ω (A t ω) - Y t ω (O t ω j))] := by
  simp [expertPseudoRegret_eq_iSup_integral_sum_sub]

/-- The pseudo-regret of the `K`-armed bandit is the pseudo-regret of the bandit with expert
advice in which the experts are the arms, each always advising its own arm. -/
lemma pseudoRegret_eq_expertPseudoRegret [DecidableEq α] (P : Measure Ω) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → α → ℝ) (T : ℕ) :
    pseudoRegret P A Y T = expertPseudoRegret P (fun _ _ ↦ diracAdvice id) A Y T := by
  simp only [pseudoRegret, expertPseudoRegret, adviceRegret_const_diracAdvice_id]

/-- The pseudo-regret is at most the expected regret against the best expert in hindsight. -/
lemma expertPseudoRegret_le_integral_iSup_adviceRegret [Finite ι] [Nonempty ι] {P : Measure Ω}
    {O : ℕ → Ω → Advice ι α} {A : ℕ → Ω → α} {Y : ℕ → Ω → α → ℝ} {T : ℕ}
    (hint : ∀ j, Integrable
      (fun ω ↦ adviceRegret (fun t ↦ O t ω) (fun t ↦ A t ω) (fun t ↦ Y t ω) T j) P)
    (hint' : Integrable
      (fun ω ↦ ⨆ j, adviceRegret (fun t ↦ O t ω) (fun t ↦ A t ω) (fun t ↦ Y t ω) T j) P) :
    expertPseudoRegret P O A Y T ≤
      P[fun ω ↦ ⨆ j, adviceRegret (fun t ↦ O t ω) (fun t ↦ A t ω) (fun t ↦ Y t ω) T j] :=
  ciSup_le fun j ↦ integral_mono (hint j) hint' fun _ ↦
    le_ciSup (f := fun j ↦ adviceRegret _ _ _ T j) (Set.finite_range _).bddAbove j

end Bandits
