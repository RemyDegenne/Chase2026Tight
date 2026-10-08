/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting

/-!
# The reduced setting on general arm and expert types

The proof of Theorem 6.1 runs the strategies of the reduced setting with `K` arms and `N` experts,
`K ≥ 2k + 1` and `N ≥ kn + 1`. We define the strategies on arbitrary arm and expert types `α` and
`ι`, through maps to the reduced types:

* `σ : α → Arm k` reduces the arms (an extra arm behaves as arm `0`), with a section
  `ρ : Arm k → α` (`σ ∘ ρ = id`);
* `τ : ι → Expert k n` reduces the experts (an extra expert behaves as expert `0`), with a section
  `τ' : Expert k n → ι` (`τ ∘ τ' = id`).

Expert `j` advises the arm `ρ (e (τ j))` when the reduced advice is `e`, and the loss of arm `a` is
the reduced loss of `σ a` (`strategyOn`). The reduced setting is the case of identity maps
(`strategyOn_id`). The lemmas of the proof are stated in this generality, so that they apply both
to the paper's statements (reduced types) and to Theorem 6.1 (`Fin K`, `Fin N`).

## Main definitions

* `liftAdvice ρ τ`, `reduceAdvice σ τ'`: advice on the general types from reduced advice, and back.
* `strategyOn σ ρ τ τ' ε θ`: the strategy `S_θ` on the general types.
* `IsGoodOn σ ρ τ τ' ε A`: good SBI algorithms on the general types.
* `pullCount σ b h`: the number of rounds of the history `h` in which an arm of batch `b` is pulled.

## Main statements

* `strategyOn_id`: `strategyOn id id id id ε θ = strategy ε θ`.
* `isGoodOn_id`: `IsGoodOn id id id id ε A ↔ IsGood ε A`.
* `strategyOn_feedbackIgnoresAction`: the losses do not depend on the arm of the current round.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Finset
open scoped ENNReal

namespace Chase2026Tight

variable {k n : ℕ} {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-! ### Advice on general types -/

/-- The advice on the general types given by the reduced advice `e`: expert `j` advises the arm
`ρ (e (τ j))`. -/
def liftAdvice (ρ : Arm k → α) (τ : ι → Expert k n) (e : Expert k n → Arm k) : ι → α :=
  fun j ↦ ρ (e (τ j))

/-- The reduced advice read from an advice `e` on the general types: the reduced expert `j` advises
the arm `σ (e (τ' j))`. -/
def reduceAdvice (σ : α → Arm k) (τ' : Expert k n → ι) (e : ι → α) : Expert k n → Arm k :=
  fun j ↦ σ (e (τ' j))

@[simp]
lemma liftAdvice_id (e : Expert k n → Arm k) : liftAdvice id id e = e := rfl

@[simp]
lemma reduceAdvice_id (e : Expert k n → Arm k) : reduceAdvice id id e = e := rfl

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] in
lemma reduceAdvice_liftAdvice {σ : α → Arm k} {ρ : Arm k → α} (hσρ : ∀ a, σ (ρ a) = a)
    {τ : ι → Expert k n} {τ' : Expert k n → ι} (hττ' : ∀ j, τ (τ' j) = j)
    (e : Expert k n → Arm k) : reduceAdvice σ τ' (liftAdvice ρ τ e) = e := by
  ext j
  simp [reduceAdvice, liftAdvice, hσρ, hττ']

omit [DiscreteMeasurableSpace α] in
@[fun_prop]
lemma measurable_liftAdvice (ρ : Arm k → α) (τ : ι → Expert k n) :
    Measurable (liftAdvice ρ τ) := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  exact (Measurable.of_discrete (f := ρ)).comp (measurable_pi_apply (τ j))

@[fun_prop]
lemma measurable_reduceAdvice (σ : α → Arm k) (τ' : Expert k n → ι) :
    Measurable (reduceAdvice (n := n) σ τ') := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  exact (Measurable.of_discrete (f := σ)).comp (measurable_pi_apply (τ' j))

/-! ### The strategies on general types -/

/-- The strategy `S_θ` of the adversary on the general types: the reduced advice process, lifted
to `ι → α`, and the reduced losses read through `σ`. -/
noncomputable def strategyOn (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) : Environment (ι → α) α (α → ℝ) where
  obs
    | 0 => Kernel.const _ ((initAdvice k n).map (liftAdvice ρ τ))
    | m + 1 => ((adviceKernel k n).comap
        (fun h ↦ (σ (h (Fin.last m)).action, reduceAdvice σ τ' (h (Fin.last m)).obs))
        (by fun_prop)).map (liftAdvice ρ τ)
  feedback _ := ((lossKernel ε θ).comap (fun p ↦ reduceAdvice σ τ' p.1.2) (by fun_prop)).map
    (fun ℓ ↦ ℓ ∘ σ)
  isMarkovKernel_obs m := by
    cases m
    · exact ⟨fun _ ↦ by rw [Kernel.const_apply]; infer_instance⟩
    · exact Kernel.IsMarkovKernel.map _ (measurable_liftAdvice ρ τ)
  isMarkovKernel_feedback _ := Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The reduced setting is the case of identity maps. -/
lemma strategyOn_id (ε : ℝ) (θ : Expert k n) :
    strategyOn (α := Arm k) (ι := Expert k n) id id id id ε θ = strategy ε θ := by
  have h1 : liftAdvice (α := Arm k) (ι := Expert k n) id id = id := rfl
  have h2 : reduceAdvice (α := Arm k) (ι := Expert k n) id id = id := rfl
  have h3 : (fun ℓ : Arm k → ℝ ↦ ℓ ∘ (id : Arm k → Arm k)) = id := rfl
  ext m : 2
  · cases m
    · simp only [strategyOn, strategy, h1, Measure.map_id]
    · simp only [strategyOn, strategy, h1, h2, Kernel.map_id]
      rfl
  · simp only [strategyOn, strategy, h2, h3, Kernel.map_id]
    rfl

/-- The losses of a round under `strategyOn` do not depend on the arm pulled in that round. -/
lemma strategyOn_feedbackIgnoresAction (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) :
    (strategyOn σ ρ τ τ' ε θ).FeedbackIgnoresAction := by
  refine fun _ ↦ ⟨((lossKernel ε θ).comap (fun p ↦ reduceAdvice σ τ' p.2) (by fun_prop)).map
    (fun ℓ ↦ ℓ ∘ σ), ?_⟩
  ext p : 1
  simp only [strategyOn, Kernel.comap_apply]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.map_apply _ (by fun_prop), Kernel.comap_apply,
    Kernel.comap_apply]

/-! ### Good SBI algorithms on general types -/

/-- An SBI algorithm on the general types is *good* if under every strategy `strategyOn … θ` it
outputs the special batch of `θ` with probability at least `0.95`. -/
def IsGoodOn [Countable α] (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (A : IdentAlg (ι → α) α ℝ (Batch k)) : Prop :=
  A.comapBanditFeedback.IsPAC (fun θ ↦ strategyOn σ ρ τ τ' ε θ)
    (fun θ b ↦ b ≠ specialBatch θ) 0.05

lemma isGoodOn_id (ε : ℝ) (A : SBIAlg k n) :
    IsGoodOn id id id id ε A ↔ IsGood ε A := by
  simp only [IsGoodOn, IsGood, SBIAlg.toIdentAlg, strategyOn_id]


/-! ### Pull counts -/

/-- The number of rounds of the history `h` in which an arm of batch `b` is pulled (an arm `a` is
in batch `(σ a).batch`). -/
def pullCount {𝓞 𝓨 : Type*} (σ : α → Arm k) (b : Batch k) {m : ℕ} (h : Hist 𝓞 α 𝓨 m) : ℕ :=
  #{i | (σ (h i).action).batch = b}

end Chase2026Tight
