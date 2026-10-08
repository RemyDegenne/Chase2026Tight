/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.PerRoundRegret
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.ExistsRun

/-!
# Reduction from special batch identification to the bandit with expert advice

The general form of Lemma 3.1, on general arm and expert types (`strategyOn`): a learner whose
pseudo-regret after `T` rounds is at most `r` under every strategy of the pool yields a good SBI
algorithm that stops after `T` rounds, as soon as `T ≥ 1000 r / ε`. The SBI algorithm runs the
learner for `T` rounds and outputs the most pulled batch (`sbiOfLearner`).

Proof: in a run against `S_θ`, the pseudo-regret is at least `ε/2` times the expected number of
rounds in which the special batch `u⋆` is not pulled
(`mul_sub_integral_pullCount_le_expertPseudoRegret`), so by Markov's inequality `u⋆` is pulled in
more than half of the `T` rounds, hence is the most pulled batch, with probability at least
`1 - 4r/(εT) ≥ 0.996`. The pseudo-regret hypothesis is about runs
on probability spaces in `Type u`: the law of the output is computed on such a run
(`exists_isAlgEnvSeq_of_finite`).

## Main definitions

* `mostPulledBatch σ a`: a batch with the largest number of pulls in the arm sequence `a`.
* `sbiOfLearner σ alg T`: the SBI algorithm of the learner `alg` (`def:sbi_of_learner`).

## Main statements

* `exists_isGoodOn_lintegral_stoppingTime_le`: the reduction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal Finset

universe u

namespace Chase2026Tight

/-! ### The SBI algorithm of a learner -/

section MostPulled

variable {k : ℕ} {α : Type*}

/-- Some batch has the largest number of pulls in the arm sequence `a`. -/
lemma exists_max_pulls (σ : α → Arm k) {m : ℕ} (a : Fin m → α) :
    ∃ b ∈ (Finset.univ : Finset (Batch k)), ∀ b' ∈ (Finset.univ : Finset (Batch k)),
      #{i | (σ (a i)).batch = b'} ≤ #{i | (σ (a i)).batch = b} :=
  Finset.univ.exists_max_image (fun b ↦ #{i | (σ (a i)).batch = b})
    ⟨Batch.zero, Finset.mem_univ _⟩

/-- A batch with the largest number of pulls in the arm sequence `a` (a fixed choice among the
most pulled batches). -/
noncomputable def mostPulledBatch (σ : α → Arm k) {m : ℕ} (a : Fin m → α) : Batch k :=
  (exists_max_pulls σ a).choose

/-- A batch pulled in more than half of the rounds is the most pulled batch. -/
lemma mostPulledBatch_eq {σ : α → Arm k} {m : ℕ} (a : Fin m → α) {b : Batch k}
    (hb : m < 2 * #{i | (σ (a i)).batch = b}) :
    mostPulledBatch σ a = b := by
  by_contra hne
  have hle := (exists_max_pulls σ a).choose_spec.2 b (Finset.mem_univ _)
  have hdisj : Disjoint (Finset.univ.filter fun i ↦ (σ (a i)).batch = b)
      (Finset.univ.filter fun i ↦ (σ (a i)).batch = mostPulledBatch σ a) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact hne (h2.symm.trans h1)
  have hcard := Finset.card_union_of_disjoint hdisj ▸ Finset.card_le_univ
    ((Finset.univ.filter fun i ↦ (σ (a i)).batch = b) ∪
      (Finset.univ.filter fun i ↦ (σ (a i)).batch = mostPulledBatch σ a))
  rw [Fintype.card_fin] at hcard
  change _ ≤ #{i | (σ (a i)).batch = mostPulledBatch σ a} at hle
  omega

/-- The most pulled batch is a measurable function of the arm sequence. -/
lemma measurable_mostPulledBatch [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (σ : α → Arm k) (m : ℕ) :
    Measurable (mostPulledBatch (m := m) σ) :=
  measurable_of_countable _

end MostPulled

section SBI

variable {k : ℕ} {𝓞 α : Type*} [MeasurableSpace 𝓞] [MeasurableSpace α] [DiscreteMeasurableSpace α]
  [Finite α] {σ : α → Arm k} {alg : Algorithm 𝓞 α ℝ} {T : ℕ}

/-- The most pulled batch of a history is a measurable function of the history. -/
lemma measurable_mostPulledBatch_hist {𝓨 : Type*} [MeasurableSpace 𝓨] (σ : α → Arm k) :
    Measurable fun h : (Σ m, Hist 𝓞 α 𝓨 m) ↦ mostPulledBatch σ fun i ↦ (h.2 i).action :=
  measurable_sigma_of_measurable_comp_mk fun _ ↦ (measurable_mostPulledBatch σ _).comp
    (measurable_pi_iff.mpr fun i ↦ Round.measurable_action.comp (measurable_pi_apply i))

/-- **The SBI algorithm of a learner** (`def:sbi_of_learner`). It runs the learner `alg` (its
sampling rule) for `T` rounds (stopping rule: the histories of length `T`), then outputs the most
pulled batch `mostPulledBatch` (deterministic output rule). -/
noncomputable def sbiOfLearner (σ : α → Arm k) (alg : Algorithm 𝓞 α ℝ) (T : ℕ) :
    IdentAlg 𝓞 α ℝ (Batch k) where
  alg := alg
  stopSet := {h | h.1 = T}
  measurableSet_stopSet := measurable_sigma_fst (measurableSet_singleton T)
  output := Kernel.deterministic _ (measurable_mostPulledBatch_hist σ)

/-- The stopping rule of the SBI algorithm of a learner: histories of length `T`. -/
lemma mem_stopSet_sbiOfLearner (m : ℕ) (h : Hist 𝓞 α (α → ℝ) m) :
    ⟨m, h⟩ ∈ (sbiOfLearner σ alg T).comapBanditFeedback.stopSet ↔ m = T := Iff.rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α}
  {Y : ℕ → Ω → α → ℝ}

/-- The SBI algorithm of a learner stops after `T` rounds. -/
lemma stoppingTime_sbiOfLearner (ω : Ω) :
    (sbiOfLearner σ alg T).comapBanditFeedback.stoppingTime O X Y ω = T := by
  rw [IdentAlg.stoppingTime_def]
  exact hittingAfter_eq_coe_iff.mpr ⟨Nat.zero_le T, (mem_stopSet_sbiOfLearner _ _).mpr rfl,
    fun j hj hmem ↦ (Set.mem_Ico.mp hj).2.ne ((mem_stopSet_sbiOfLearner _ _).mp hmem)⟩

/-- The history played by the SBI algorithm of a learner is the history of the first `T`
rounds. -/
lemma stoppedHist_sbiOfLearner (ω : Ω) :
    (sbiOfLearner σ alg T).comapBanditFeedback.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩ := by
  rw [IdentAlg.stoppedHist_def]
  simp only [stoppedValue, stoppingTime_sbiOfLearner]
  rfl

/-- The runs of the SBI algorithm of a learner are the runs of the learner, with output the most
pulled batch in the first `T` rounds. -/
lemma isRun_sbiOfLearner {env : Environment 𝓞 α (α → ℝ)} {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O X Y alg.comapBanditFeedback env P) :
    (sbiOfLearner σ alg T).comapBanditFeedback.IsRun env O X Y
      (fun ω ↦ mostPulledBatch σ fun i : Fin T ↦ X i ω) P := by
  refine ⟨by rw [IdentAlg.comapBanditFeedback_alg]; exact h, ?_⟩
  set g : (Σ m, Hist 𝓞 α (α → ℝ) m) → Batch k := fun h ↦ mostPulledBatch σ fun i ↦ (h.2 i).action
  have hg : Measurable g := measurable_mostPulledBatch_hist σ
  have h_out : (sbiOfLearner σ alg T).comapBanditFeedback.output = Kernel.deterministic g hg := by
    ext x : 1
    rcases x with ⟨m, x⟩
    exact IdentAlg.comapPartialFeedback_output_mk _ _ _ m x
  have h_hist : (sbiOfLearner σ alg T).comapBanditFeedback.stoppedHist O X Y
      = fun ω ↦ ⟨T, history O X Y T ω⟩ := funext stoppedHist_sbiOfLearner
  rw [h_out, h_hist]
  exact hasCondDistrib_comp_self hg
    ((measurable_sigma_mk T).comp (h.measurable_history T)).aemeasurable

end SBI

/-! ### The reduction -/

variable {k n : ℕ} {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
  [DecidableEq α] [Finite ι] {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n}
  {τ' : Expert k n → ι}

/-- **Reduction from SBI to BwE** (`lem:reduction`), on general types. Let `alg` be a learner
whose pseudo-regret after `T ≥ 1` rounds is at most `r` under every strategy of the pool, with
`T ≥ 1000 r / ε`. Then there is a good SBI algorithm whose expected number of rounds is at most `T`
under every strategy of the pool. -/
lemma exists_isGoodOn_lintegral_stoppingTime_le (hσρ : ∀ a, σ (ρ a) = a)
    (hττ' : ∀ j, τ (τ' j) = j) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1) (alg : Algorithm (ι → α) α ℝ)
    {T : ℕ} (hT1 : 1 ≤ T) {r : ℝ}
    (hr : ∀ (θ : Expert k n) {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → ι → α) (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ),
      IsAlgEnvSeq O A Y alg.comapBanditFeedback (strategyOn σ ρ τ τ' ε θ) P →
        expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T ≤ r)
    (hT : 1000 * r / ε ≤ T) :
    ∃ A' : IdentAlg (ι → α) α ℝ (Batch k), IsGoodOn σ ρ τ τ' ε A' ∧
      ∀ (θ : Expert k n) {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
        [IsProbabilityMeasure P] (O : ℕ → Ω → ι → α) (X : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ)
        (out : Ω → Batch k),
        A'.comapBanditFeedback.IsRun (strategyOn σ ρ τ τ' ε θ) O X Y out P →
          ∫⁻ ω, (A'.comapBanditFeedback.stoppingTime O X Y ω : ℝ≥0∞) ∂P ≤ T := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 / 2 := hε.2.trans (by norm_num)
  refine ⟨sbiOfLearner σ alg T, fun θ ↦ ?_, fun θ Ω _ P _ O X Y out _ ↦ ?_⟩
  swap
  · simp_rw [stoppingTime_sbiOfLearner]
    simp
  -- a run of the learner on a probability space in `Type u`
  obtain ⟨Ω, _, P, _, O, X, Y, h⟩ :=
    exists_isAlgEnvSeq_of_finite.{u} alg.comapBanditFeedback (strategyOn σ ρ τ τ' ε θ)
  have hrun := isRun_sbiOfLearner (σ := σ) (T := T) h
  have hbad : MeasurableSet {d : Batch k | d ≠ specialBatch θ} := MeasurableSet.of_discrete
  change ((sbiOfLearner σ alg T).comapBanditFeedback.outputMeasure
    (strategyOn σ ρ τ τ' ε θ)).real {d | d ≠ specialBatch θ} ≤ 0.05
  rw [← hrun.hasLaw_output.measureReal_eq hbad]
  -- the number of pulls of the special batch
  set N : Ω → ℝ := fun ω ↦ (pullCount σ (specialBatch θ) (history O X Y T ω) : ℝ) with hN
  have hN_meas : Measurable N := by
    change Measurable ((fun a : Fin T → α ↦ (#{i | (σ (a i)).batch = specialBatch θ} : ℝ)) ∘
      fun ω i ↦ X i ω)
    exact (measurable_of_countable _).comp (measurable_pi_iff.mpr fun i ↦ h.measurable_action i)
  have hN_le (ω : Ω) : N ω ≤ T := by
    have : pullCount σ (specialBatch θ) (history O X Y T ω) ≤ T :=
      (Finset.card_le_univ _).trans (Fintype.card_fin T).le
    simp only [hN]
    exact_mod_cast this
  have hN_int : Integrable N P :=
    Integrable.of_mem_Icc 0 T hN_meas.aemeasurable
      (ae_of_all _ fun ω ↦ ⟨Nat.cast_nonneg _, hN_le ω⟩)
  -- Markov's inequality for the number of rounds in which the special batch is not pulled
  have h_markov := mul_meas_ge_le_integral_of_nonneg (f := fun ω ↦ (T : ℝ) - N ω)
    (ae_of_all _ fun ω ↦ sub_nonneg.mpr (hN_le ω)) ((integrable_const _).sub hN_int) ((T : ℝ) / 2)
  rw [integral_sub (integrable_const _) hN_int, integral_const, probReal_univ, one_smul] at h_markov
  -- if the special batch is pulled in more than half of the rounds, it is the output
  have h_sub : (fun ω ↦ mostPulledBatch σ fun i : Fin T ↦ X i ω) ⁻¹' {d | d ≠ specialBatch θ}
      ⊆ {ω | (T : ℝ) / 2 ≤ T - N ω} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    refine hω (mostPulledBatch_eq _ ?_)
    have : (T : ℝ) < 2 * N ω := by linarith [not_le.mp hlt]
    simp only [hN] at this
    exact_mod_cast this
  have h_regret : ε / 2 * (T - ∫ ω, N ω ∂P) ≤ r :=
    (mul_sub_integral_pullCount_le_expertPseudoRegret hσρ hττ' h hε0.le hε1 T).trans
      (hr θ P O X Y h)
  have hr' : 1000 * r ≤ T * ε := (div_le_iff₀ hε0).mp hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  set p := P.real {ω | (T : ℝ) / 2 ≤ T - N ω}
  have hp : p ≤ 1 / 250 := by
    have h1 : ε / 2 * (T / 2 * p) ≤ ε / 2 * (T - ∫ ω, N ω ∂P) :=
      mul_le_mul_of_nonneg_left h_markov (by positivity)
    by_contra hcon
    nlinarith [mul_pos hε0 hT0, not_le.mp hcon]
  calc P.real ((fun ω ↦ mostPulledBatch σ fun i : Fin T ↦ X i ω) ⁻¹' {d | d ≠ specialBatch θ})
  _ ≤ p := measureReal_mono h_sub
  _ ≤ 0.05 := by linarith

end Chase2026Tight
