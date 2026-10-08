/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StoppedHistory

/-!
# The law of a stopped history is determined by the laws of the histories before stopping

Let `S` be a stopping rule (a measurable set of histories of variable length). The history stopped
by `S` is a function of the whole sequence of rounds, but its law only depends on the laws of the
histories of `L` rounds restricted to the histories along which the interaction has not stopped
before round `L` (`preStop S L`, no proper prefix in `S`): two measures on the sequences of rounds
that agree on these events give the same law to the stopped history
(`map_stoppedHist_eq_of_forall_preStop`). This allows to compare the laws of stopped histories of
algorithm-environment pairs that only agree before stopping.

## Main definitions

* `preStop S L`: the histories of `L` rounds none of whose proper prefixes belongs to `S`.
* `IT.stoppedHist S`: the history stopped by `S` on the canonical space of sequences of rounds.

## Main statements

* `map_stoppedHist_eq_of_forall_preStop`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The histories of `L` rounds none of whose proper prefixes (the histories of the first `m < L`
rounds) belongs to `S`: the histories along which an interaction stopped by `S` lasts at least `L`
rounds. -/
def preStop (S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)) (L : ℕ) : Set (Hist 𝓞 𝓐 𝓨 L) :=
  {h | ∀ m (hm : m < L), (⟨m, fun i ↦ h (Fin.castLE hm.le i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S}

/-- The histories along which the interaction has not stopped form a measurable set. -/
lemma measurableSet_preStop {S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)} (hS : MeasurableSet S) (L : ℕ) :
    MeasurableSet (preStop S L) := by
  have : preStop S L = ⋂ m : Fin L, (fun h : Hist 𝓞 𝓐 𝓨 L ↦
      (⟨m, fun i ↦ h (Fin.castLE m.2.le i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' Sᶜ := by
    ext h
    simp only [preStop, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
    exact ⟨fun h' m ↦ h' m m.2, fun h' m hm ↦ h' ⟨m, hm⟩⟩
  rw [this]
  refine MeasurableSet.iInter fun m ↦ ?_
  exact ((measurable_sigma_mk (m : ℕ)).comp (by fun_prop)) hS.compl

namespace IT

/-- The history stopped by `S` on the canonical space of sequences of rounds. -/
noncomputable def stoppedHist (S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)) :
    (ℕ → Round 𝓞 𝓐 𝓨) → Σ n, Hist 𝓞 𝓐 𝓨 n :=
  stoppedValue (sigmaHistory obs action feedback)
    (hittingAfter (sigmaHistory obs action feedback) S 0)

/-- The stopped history on the canonical space is measurable. -/
lemma measurable_stoppedHist {S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)} (hS : MeasurableSet S) :
    Measurable (stoppedHist S) :=
  measurable_stoppedValue_sigmaHistory measurable_obs measurable_action measurable_feedback
    (measurable_hittingAfter_sigmaHistory measurable_obs measurable_action measurable_feedback hS)

end IT

/-- The law of the stopped history is the image of the law of the sequence of rounds. -/
lemma stoppedHistMeasure_eq_map (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨)
    (S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)) :
    stoppedHistMeasure alg env S = (trajMeasure alg env).map (IT.stoppedHist S) := rfl

section Decomposition

variable {S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)}

/-- The hitting time of `S` on the canonical space. -/
local notation "τS" => hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0

/-- The interaction stops after `m` rounds iff the history of the first `m` rounds is in `S`
and none of its proper prefixes is. -/
lemma hittingAfter_sigmaHistory_eq_coe_iff (m : ℕ) (ω : ℕ → Round 𝓞 𝓐 𝓨) :
    τS ω = m ↔ (⟨m, IT.hist m ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ S ∧ IT.hist m ω ∈ preStop S m := by
  rw [Nat.cast_withTop, hittingAfter_eq_coe_iff]
  simp only [zero_le, true_and, Set.mem_Ico, preStop, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h j hj⟩

/-- The interaction lasts at least `L` rounds iff no proper prefix of the history of the first
`L` rounds is in `S`. -/
lemma coe_le_hittingAfter_sigmaHistory_iff (L : ℕ) (ω : ℕ → Round 𝓞 𝓐 𝓨) :
    (L : WithTop ℕ) ≤ τS ω ↔ IT.hist L ω ∈ preStop S L := by
  rw [← not_lt, Nat.cast_withTop, hittingAfter_lt_iff]
  simp only [Set.mem_Ico, zero_le, true_and, not_exists, not_and, preStop, Set.mem_ofPred_eq]
  exact ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h j hj⟩

/-- The interaction never stops iff it lasts at least `L` rounds for every `L`. -/
lemma hittingAfter_sigmaHistory_eq_top_iff (ω : ℕ → Round 𝓞 𝓐 𝓨) :
    τS ω = ⊤ ↔ ∀ L : ℕ, (L : WithTop ℕ) ≤ τS ω := by
  refine ⟨fun h L ↦ by simp [h], fun h ↦ ?_⟩
  by_contra h_ne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_ne
  have := h (m + 1)
  rw [← hm, Nat.cast_withTop] at this
  exact absurd (WithTop.coe_le_coe.mp this) (by omega)

end Decomposition

/-- **The law of the stopped history is determined by the laws before stopping.** If two finite
measures on the sequences of rounds agree on the events `{IT.hist L ∈ G}` for the measurable sets
`G` of histories of `L` rounds along which the interaction has not stopped before round `L`, then
the history stopped by `S` has the same law under both. -/
lemma map_stoppedHist_eq_of_forall_preStop {P Q : Measure (ℕ → Round 𝓞 𝓐 𝓨)}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)}
    (hS : MeasurableSet S)
    (h : ∀ L (G : Set (Hist 𝓞 𝓐 𝓨 L)), MeasurableSet G → G ⊆ preStop S L →
      P (IT.hist L ⁻¹' G) = Q (IT.hist L ⁻¹' G)) :
    P.map (IT.stoppedHist S) = Q.map (IT.stoppedHist S) := by
  set τ := hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 with hτ_def
  have hτ : Measurable τ :=
    measurable_hittingAfter_sigmaHistory IT.measurable_obs IT.measurable_action
      IT.measurable_feedback hS
  set c : ℕ := (⊤ : WithTop ℕ).untopA with hc
  ext A hA
  rw [Measure.map_apply (IT.measurable_stoppedHist hS) hA,
    Measure.map_apply (IT.measurable_stoppedHist hS) hA]
  -- the events of stopping at `m` with the stopped history in `A`
  set E : ℕ → Set (ℕ → Round 𝓞 𝓐 𝓨) := fun m ↦ IT.hist m ⁻¹'
    {h | (⟨m, h⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A ∧ (⟨m, h⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ S ∧
      h ∈ preStop S m} with hE
  -- the events of not stopping before `N + c + 1` with the history of `c` rounds in `A`
  set F : ℕ → Set (ℕ → Round 𝓞 𝓐 𝓨) := fun N ↦ IT.hist (N + c + 1) ⁻¹'
    {h | h ∈ preStop S (N + c + 1) ∧
      (⟨c, fun i ↦ h (Fin.castLE (by omega) i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A} with hF
  have hEm : ∀ m, MeasurableSet {h : Hist 𝓞 𝓐 𝓨 m | (⟨m, h⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A ∧
      (⟨m, h⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ S ∧ h ∈ preStop S m} := fun m ↦
    ((measurable_sigma_mk m) hA).inter (((measurable_sigma_mk m) hS).inter
      (measurableSet_preStop hS m))
  have hFm : ∀ N, MeasurableSet {h : Hist 𝓞 𝓐 𝓨 (N + c + 1) | h ∈ preStop S (N + c + 1) ∧
      (⟨c, fun i ↦ h (Fin.castLE (by omega) i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A} := fun N ↦
    (measurableSet_preStop hS _).inter (((measurable_sigma_mk c).comp (by fun_prop)) hA)
  have hE_meas : ∀ m, MeasurableSet (E m) := fun m ↦ IT.measurable_hist m (hEm m)
  have hF_meas : ∀ N, MeasurableSet (F N) := fun N ↦ IT.measurable_hist _ (hFm N)
  -- `E m` is the event `τ = m` with the stopped history in `A`
  have hE_eq : ∀ m, E m = {ω | τ ω = m ∧ (⟨m, IT.hist m ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A} := by
    intro m
    ext ω
    simp only [hE, Set.mem_preimage, Set.mem_ofPred_eq, hτ_def,
      hittingAfter_sigmaHistory_eq_coe_iff]
    tauto
  -- `F N` is the event `N + c + 1 ≤ τ` with the history of the first `c` rounds in `A`
  have hF_eq : ∀ N, F N = {ω | ((N + c + 1 : ℕ) : WithTop ℕ) ≤ τ ω ∧
      (⟨c, IT.hist c ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A} := by
    intro N
    ext ω
    simp only [hF, Set.mem_preimage, Set.mem_ofPred_eq, hτ_def,
      coe_le_hittingAfter_sigmaHistory_iff]
    rfl
  have hF_anti : Antitone F := by
    intro N N' hNN' ω hω
    rw [hF_eq] at hω ⊢
    exact ⟨le_trans (by exact_mod_cast (by omega : N + c + 1 ≤ N' + c + 1)) hω.1, hω.2⟩
  have hF_inter : ⋂ N, F N = {ω | τ ω = ⊤ ∧ (⟨c, IT.hist c ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A} := by
    ext ω
    simp only [Set.mem_iInter, hF_eq, Set.mem_ofPred_eq]
    rw [hittingAfter_sigmaHistory_eq_top_iff]
    refine ⟨fun h ↦ ⟨fun L ↦ ?_, (h 0).2⟩, fun h N ↦ ⟨h.1 _, h.2⟩⟩
    exact le_trans (by exact_mod_cast (by omega : L ≤ L + c + 1)) (h L).1
  -- decomposition of the event `IT.stoppedHist S ∈ A`
  have h_decomp : IT.stoppedHist S ⁻¹' A = (⋃ m, E m) ∪ ⋂ N, F N := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, hE_eq, hF_inter,
      Set.mem_ofPred_eq, IT.stoppedHist, stoppedValue]
    by_cases h_top : τ ω = ⊤
    · rw [← hτ_def, h_top]
      have h_no : ¬ ∃ i : ℕ, (⊤ : WithTop ℕ) = i ∧
          (⟨i, IT.hist i ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A := by
        rintro ⟨i, hi, -⟩
        exact WithTop.natCast_ne_top i hi.symm
      simp only [h_no, true_and, false_or]
      rfl
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_top
      rw [← hτ_def, ← hm, ← Nat.cast_withTop]
      simp only [Nat.cast_inj, exists_eq_left', WithTop.natCast_ne_top, false_and, or_false]
      rfl
  have h_disj : Pairwise (Function.onFun Disjoint E) := by
    intro m m' hmm'
    rw [Function.onFun, hE_eq, hE_eq]
    refine Set.disjoint_left.mpr fun ω h1 h2 ↦ hmm' ?_
    exact_mod_cast h1.1.symm.trans h2.1
  have h_disj' : Disjoint (⋃ m, E m) (⋂ N, F N) := by
    rw [hF_inter, Set.disjoint_iUnion_left]
    intro m
    rw [hE_eq]
    exact Set.disjoint_left.mpr fun ω h1 h2 ↦ by simp [h1.1] at h2
  have h_meas : ∀ μ : Measure (ℕ → Round 𝓞 𝓐 𝓨), μ (IT.stoppedHist S ⁻¹' A) =
      ∑' m, μ (E m) + μ (⋂ N, F N) := by
    intro μ
    rw [h_decomp, measure_union h_disj' (MeasurableSet.iInter hF_meas),
      measure_iUnion h_disj hE_meas]
  have hEPQ : ∀ m, P (E m) = Q (E m) := fun m ↦ h m _ (hEm m) fun _ hx ↦ hx.2.2
  have hFPQ : ∀ N, P (F N) = Q (F N) := fun N ↦ h _ _ (hFm N) fun _ hx ↦ hx.1
  have hP_lim := tendsto_measure_iInter_atTop (μ := P) (fun N ↦ (hF_meas N).nullMeasurableSet)
    hF_anti ⟨0, measure_ne_top _ _⟩
  have hQ_lim := tendsto_measure_iInter_atTop (μ := Q) (fun N ↦ (hF_meas N).nullMeasurableSet)
    hF_anti ⟨0, measure_ne_top _ _⟩
  have h_inter : P (⋂ N, F N) = Q (⋂ N, F N) := by
    refine tendsto_nhds_unique hP_lim ?_
    convert hQ_lim using 1
    funext N
    exact hFPQ N
  rw [h_meas P, h_meas Q, h_inter]
  simp_rw [hEPQ]

end Learning
