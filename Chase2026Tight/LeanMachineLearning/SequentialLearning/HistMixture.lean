/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.LeanMachineLearning.SequentialLearning.StoppedHistLaw

/-!
# Mixture representations of the laws of histories in countable settings

When the observation, action and feedback spaces are countable with measurable singletons, the
law of the history of the first `L + 1` rounds is computed from the law of the history of the first
`L` rounds and the step kernel: `P(H_{L+1} = h ⧺ r) = P(H_L = h) · step_L(h)({r})`
(`trajMeasure_hist_snoc`).

We use this one-step formula to represent the law of the histories of an algorithm in an
environment `env` as a mixture, over a parameter `t` with law `ρ`, of the laws of the histories in
environments `envT t`: if, along the histories of a set `D`, the step probabilities of `envT t`
are a factor `g` times the indicator of a constraint set `C` on the parameter, and the step
probabilities of `env` are the same factor times the conditional probability under `ρ` of the new
constraint, then the law of the histories in `D` is the mixture
(`trajMeasure_hist_eq_lintegral_of_factor`). If moreover the histories along which an
interaction stopped by `S` has not yet stopped belong to `D`, the law of the stopped history is
the mixture of the laws of the stopped histories (`stoppedHistMeasure_eq_comp_of_factor`).

This is the formal counterpart of a *tape* argument: the environments `envT t` read their
randomness from a tape `t` drawn beforehand with law `ρ`, while `env` draws it when needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The history of `L + 1` rounds on the canonical space is the history of the first `L` rounds
followed by the round `L`. -/
lemma IT.hist_add_one_eq_snoc (L : ℕ) (ω : ℕ → Round 𝓞 𝓐 𝓨) :
    IT.hist (L + 1) ω = Fin.snoc (IT.hist L ω) (IT.step L ω) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp [IT.hist, IT.step]
  · simp [IT.hist]

/-- The law of the history of `0` rounds is the Dirac mass at the empty history. -/
lemma trajMeasure_hist_zero (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨)
    (h : Hist 𝓞 𝓐 𝓨 0) :
    trajMeasure alg env (IT.hist 0 ⁻¹' {h}) = 1 := by
  have : IT.hist 0 ⁻¹' {h} = (Set.univ : Set (ℕ → Round 𝓞 𝓐 𝓨)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [this, measure_univ]

variable [MeasurableSingletonClass 𝓞] [MeasurableSingletonClass 𝓐] [MeasurableSingletonClass 𝓨]

/-- The step kernel of a round with countable spaces, on a singleton. -/
lemma stepKernel_singleton (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨) (n : ℕ)
    (h : Hist 𝓞 𝓐 𝓨 n) (o : 𝓞) (a : 𝓐) (y : 𝓨) :
    stepKernel alg env n h {(o, a, y)} =
      env.obs n h {o} * alg.policy n (h, o) {a} * env.feedback n ((h, o), a) {y} := by
  have h1 : ({(o, a, y)} : Set (𝓞 × 𝓐 × 𝓨)) = {o} ×ˢ ({a} ×ˢ {y}) := by simp
  have h2 : ({(a, y)} : Set (𝓐 × 𝓨)) = {a} ×ˢ {y} := by simp
  rw [stepKernel, h1, Kernel.compProd_apply_prod (measurableSet_singleton _)
      ((measurableSet_singleton _).prod (measurableSet_singleton _)), lintegral_singleton,
    Kernel.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton]
  ring

/-- **One-step formula** for the law of the histories with countable spaces. -/
lemma trajMeasure_hist_snoc (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨) (L : ℕ)
    (h : Hist 𝓞 𝓐 𝓨 L) (r : Round 𝓞 𝓐 𝓨) :
    trajMeasure alg env (IT.hist (L + 1) ⁻¹' {Fin.snoc h r}) =
      trajMeasure alg env (IT.hist L ⁻¹' {h}) * stepKernel alg env L h {r} := by
  have h_pre : IT.hist (L + 1) ⁻¹' {Fin.snoc h r} =
      (fun ω ↦ (IT.hist L ω, IT.step L ω)) ⁻¹' ({h} ×ˢ {r}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, IT.hist_add_one_eq_snoc,
      Set.singleton_prod_singleton, Prod.mk.injEq]
    exact Fin.snoc_inj
  have h_law := (IT.hasCondDistrib_step alg env L).map_eq
  rw [h_pre, ← Measure.map_apply (by fun_prop)
    ((measurableSet_singleton _).prod (measurableSet_singleton _)), h_law,
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply (IT.measurable_hist L) (measurableSet_singleton _),
    mul_comm]

section Mixture

variable [Countable 𝓞] [Countable 𝓐] [Countable 𝓨]

variable {T : Type*} {mT : MeasurableSpace T} [Countable T] [MeasurableSingletonClass T]
  {ρ : Measure T} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {envT : T → Environment 𝓞 𝓐 𝓨} {D : ∀ L, Set (Hist 𝓞 𝓐 𝓨 L)}
  {C : ∀ L, Hist 𝓞 𝓐 𝓨 L → Set T} {g : ∀ L, Hist 𝓞 𝓐 𝓨 L → Round 𝓞 𝓐 𝓨 → ℝ≥0∞}

omit [Countable 𝓞] [Countable 𝓐] [Countable 𝓨] [Countable T] [MeasurableSingletonClass T] in
/-- Induction step of the mixture representation: along the histories of `D`, the probability of
a history under `envT t` is a factor times the indicator of the constraint set `C L h`, and under
`env` it is the same factor times `ρ (C L h)`. -/
lemma exists_trajMeasure_hist_eq_of_factor [IsProbabilityMeasure ρ]
    (hD : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → h ∈ D L)
    (hC0 : ∀ h, C 0 h = Set.univ)
    (hC : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, C (L + 1) (Fin.snoc h r) ⊆ C L h)
    (hT : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → ∀ t ∈ C L h,
      stepKernel alg (envT t) L h {r} = g L h r * (C (L + 1) (Fin.snoc h r)).indicator 1 t)
    (hE : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) →
      stepKernel alg env L h {r} * ρ (C L h) = g L h r * ρ (C (L + 1) (Fin.snoc h r)))
    (L : ℕ) (h : Hist 𝓞 𝓐 𝓨 L) (hh : h ∈ D L) :
    ∃ G : ℝ≥0∞, (∀ t, trajMeasure alg (envT t) (IT.hist L ⁻¹' {h}) = G * (C L h).indicator 1 t) ∧
      trajMeasure alg env (IT.hist L ⁻¹' {h}) = G * ρ (C L h) := by
  induction L with
  | zero =>
    refine ⟨1, fun t ↦ ?_, ?_⟩
    · rw [trajMeasure_hist_zero, hC0, Set.indicator_univ, Pi.one_apply, one_mul]
    · rw [trajMeasure_hist_zero, hC0, measure_univ, one_mul]
  | succ L ih =>
    obtain ⟨h, r, rfl⟩ : ∃ h' r, h = Fin.snoc h' r :=
      ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
    obtain ⟨G, hGT, hGE⟩ := ih h (hD L _ _ hh)
    refine ⟨G * g L h r, fun t ↦ ?_, ?_⟩
    · rw [trajMeasure_hist_snoc, hGT]
      by_cases ht : t ∈ C L h
      · rw [hT L _ _ hh t ht, Set.indicator_of_mem ht, Pi.one_apply, mul_one, mul_assoc]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem fun h' ↦ ht (hC L _ _ h'),
          mul_zero, zero_mul, mul_zero]
    · rw [trajMeasure_hist_snoc, hGE, mul_assoc, mul_comm (ρ _), hE L _ _ hh, ← mul_assoc]

omit [Countable 𝓞] [Countable 𝓐] [Countable 𝓨] in
/-- **Mixture representation of the laws of histories.** Along the histories of `D`, the law of
the history of `L` rounds of `alg` in `env` is the mixture over `t ∼ ρ` of its laws in the
environments `envT t`, if the step probabilities factor through constraint sets on the parameter
as in `exists_trajMeasure_hist_eq_of_factor`. -/
lemma trajMeasure_hist_eq_lintegral_of_factor [IsProbabilityMeasure ρ]
    (hD : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → h ∈ D L)
    (hC0 : ∀ h, C 0 h = Set.univ)
    (hC : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, C (L + 1) (Fin.snoc h r) ⊆ C L h)
    (hT : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → ∀ t ∈ C L h,
      stepKernel alg (envT t) L h {r} = g L h r * (C (L + 1) (Fin.snoc h r)).indicator 1 t)
    (hE : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) →
      stepKernel alg env L h {r} * ρ (C L h) = g L h r * ρ (C (L + 1) (Fin.snoc h r)))
    (L : ℕ) (h : Hist 𝓞 𝓐 𝓨 L) (hh : h ∈ D L) :
    trajMeasure alg env (IT.hist L ⁻¹' {h}) =
      ∫⁻ t, trajMeasure alg (envT t) (IT.hist L ⁻¹' {h}) ∂ρ := by
  obtain ⟨G, hGT, hGE⟩ := exists_trajMeasure_hist_eq_of_factor hD hC0 hC hT hE L h hh
  simp_rw [hGT]
  rw [hGE, lintegral_const_mul _ (measurable_one.indicator (Set.Countable.measurableSet
    (Set.to_countable _))), lintegral_indicator_one (Set.Countable.measurableSet
    (Set.to_countable _))]

/-- The kernel giving the law of the sequence of rounds of `alg` in `envT t`. -/
noncomputable def trajKernel (alg : Algorithm 𝓞 𝓐 𝓨) (envT : T → Environment 𝓞 𝓐 𝓨) :
    Kernel T (ℕ → Round 𝓞 𝓐 𝓨) :=
  Kernel.ofFunOfCountable fun t ↦ trajMeasure alg (envT t)

instance : IsMarkovKernel (trajKernel alg envT) :=
  ⟨fun t ↦ inferInstanceAs (IsProbabilityMeasure (trajMeasure alg (envT t)))⟩

/-- The kernel giving the law of the history stopped by `S` of `alg` in `envT t`. -/
noncomputable def stoppedHistKernel (alg : Algorithm 𝓞 𝓐 𝓨) (envT : T → Environment 𝓞 𝓐 𝓨)
    (S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)) : Kernel T (Σ n, Hist 𝓞 𝓐 𝓨 n) :=
  Kernel.ofFunOfCountable fun t ↦ stoppedHistMeasure alg (envT t) S

instance (S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)) : IsMarkovKernel (stoppedHistKernel alg envT S) :=
  ⟨fun t ↦ inferInstanceAs (IsProbabilityMeasure (stoppedHistMeasure alg (envT t) S))⟩

/-- **Mixture representation of the law of a stopped history.** If the step probabilities factor
through constraint sets on the parameter along the histories of `D` (as in
`exists_trajMeasure_hist_eq_of_factor`), and the histories along which the interaction stopped by
`S` has not yet stopped belong to `D`, then the law of the history of `alg` in `env` stopped by
`S` is the mixture over `t ∼ ρ` of its laws in the environments `envT t`. -/
lemma stoppedHistMeasure_eq_comp_of_factor [IsProbabilityMeasure ρ]
    {S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)} (hS : MeasurableSet S)
    (hD : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → h ∈ D L)
    (hC0 : ∀ h, C 0 h = Set.univ)
    (hC : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, C (L + 1) (Fin.snoc h r) ⊆ C L h)
    (hT : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) → ∀ t ∈ C L h,
      stepKernel alg (envT t) L h {r} = g L h r * (C (L + 1) (Fin.snoc h r)).indicator 1 t)
    (hE : ∀ L (h : Hist 𝓞 𝓐 𝓨 L) r, Fin.snoc h r ∈ D (L + 1) →
      stepKernel alg env L h {r} * ρ (C L h) = g L h r * ρ (C (L + 1) (Fin.snoc h r)))
    (hPre : ∀ L, preStop S L ⊆ D L) :
    stoppedHistMeasure alg env S = stoppedHistKernel alg envT S ∘ₘ ρ := by
  have h_comp : stoppedHistKernel alg envT S ∘ₘ ρ =
      (trajKernel alg envT ∘ₘ ρ).map (IT.stoppedHist S) := by
    rw [Measure.map_comp _ _ (IT.measurable_stoppedHist hS)]
    congr 1
    ext t : 1
    rw [Kernel.map_apply _ (IT.measurable_stoppedHist hS)]
    rfl
  rw [h_comp, stoppedHistMeasure_eq_map]
  refine map_stoppedHist_eq_of_forall_preStop hS fun L G _ hG ↦ ?_
  have hcount : G.Countable := Set.to_countable G
  have hsing : ∀ y ∈ G, MeasurableSet (IT.hist (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) L ⁻¹' {y}) :=
    fun y _ ↦ IT.measurable_hist L (measurableSet_singleton y)
  rw [Measure.bind_apply (IT.measurable_hist L (Set.Countable.measurableSet hcount))
      (Kernel.aemeasurable _), ← tsum_measure_preimage_singleton hcount hsing]
  simp_rw [← tsum_measure_preimage_singleton hcount hsing]
  rw [lintegral_tsum fun _ ↦ (Kernel.measurable_coe _ (hsing _ (Subtype.prop _))).aemeasurable]
  refine tsum_congr fun y ↦ ?_
  exact trajMeasure_hist_eq_lintegral_of_factor hD hC0 hC hT hE L y (hPre L (hG y.2))

end Mixture

end Learning
