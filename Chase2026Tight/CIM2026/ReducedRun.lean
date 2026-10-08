/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Embedding
public import Chase2026Tight.LeanMachineLearning.Online.Bandit.Adversarial
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.RunTransport

/-!
# Runs of an SBI algorithm in the finite reduced setting

An SBI algorithm `B` on the general types (advice `ι → α`, arms `α`, losses in `ℝ`) run with
bandit feedback against `strategyOn σ ρ τ τ' ε θ` only sees advice of the form
`liftAdvice ρ τ (adviceOf b)` for advice bits `b : Bits k n` and losses in `{0, 1}`. We transport
its runs to the *reduced setting*, with finite observations `Bits k n` and Boolean feedbacks
(whether the loss of the pulled arm is `1`): the reduced strategy `redStrategy σ ε θ` draws the
advice bits as the advice process of `S_θ` and the loss bit of the pulled arm as `S_θ`, and the
reduced algorithm `reducedAlg ρ τ B` reads the bits through `liftAdvice ρ τ ∘ adviceOf` and the
loss bits as losses `0` or `1`.

The output of `B` against `strategyOn σ ρ τ τ' ε θ` has the law of the output of the reduced
algorithm against the reduced strategy (`outputMeasure_comapBanditFeedback_strategyOn`), in two
steps: the losses of the arms that are not pulled are forgotten
(`IdentAlg.outputMeasure_comapPartialFeedback`, with the environment `banditStrategyOn` of the
losses of the pulled arms), and a run in the reduced setting is lifted to the general types
(`IdentAlg.outputMeasure_comapObsFeedback`).

## Main definitions

* `refreshBits I b f`: the advice bits after a round in which arm `I` is pulled.
* `lossBit θ b r a`: whether the loss of arm `a` is `1`.
* `redStrategy σ ε θ`: the reduced strategy, an environment on `Bits k n`, `α`, `Bool`.
* `reducedAlg ρ τ B`: the reduced SBI algorithm.

## Main statements

* `outputMeasure_comapBanditFeedback_strategyOn`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

variable {k n : ℕ} {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]

/-! ### Advice bits and loss bits -/

/-- The advice bits of the round after a round with advice bits `b` in which the arm `I` is
pulled, when the fresh bits are `f`: the bits of the batch of `I` are those of `f`, the others
are kept. -/
def refreshBits (I : Arm k) (b f : Bits k n) : Bits k n :=
  fun u ↦ if I.inBatch u then f u else b u

/-- The advice bits of the advice given by bits `b` are `b`. -/
@[simp]
lemma bitsOf_adviceOf_eq_self (b : Bits k n) : bitsOf (adviceOf b) = b := by
  funext u v
  rfl

/-- Whether the loss of arm `a` is `1` under `S_θ`, for the advice bits `b` and the randomness
`r` of the round. -/
noncomputable def lossBit (θ : Expert k n) (b : Bits k n) (r : Bool × (Fin k → Bool) × Bool)
    (a : Arm k) : Bool :=
  decide (lossOf θ (adviceOf b) r a = 1)

/-- The real loss `0` or `1` given by a loss bit. -/
def boolLoss (y : Bool) : ℝ := if y then 1 else 0

/-- The losses are `0` or `1`. -/
lemma lossOf_eq_zero_or_eq_one (θ : Expert k n) (e : Expert k n → Arm k)
    (r : Bool × (Fin k → Bool) × Bool) (a : Arm k) :
    lossOf θ e r a = 0 ∨ lossOf θ e r a = 1 := by
  unfold lossOf
  rcases (a : Option (Fin k × Bool)) with _ | ⟨u, b⟩
  · by_cases h : r.1 <;> simp [h]
  · by_cases h : b = correctArm θ e r u <;> simp [h]

/-- The real loss given by the loss bit of an arm is its loss. -/
@[simp]
lemma boolLoss_lossBit (θ : Expert k n) (b : Bits k n) (r : Bool × (Fin k → Bool) × Bool)
    (a : Arm k) : boolLoss (lossBit θ b r a) = lossOf θ (adviceOf b) r a := by
  rcases lossOf_eq_zero_or_eq_one θ (adviceOf b) r a with h | h <;> simp [lossBit, boolLoss, h]

/-- The advice on the general types given by advice bits. -/
def liftBits (ρ : Arm k → α) (τ : ι → Expert k n) (b : Bits k n) : ι → α :=
  liftAdvice ρ τ (adviceOf b)

omit [DiscreteMeasurableSpace α] [Countable α] in
/-- The advice given by advice bits is a measurable function of the bits. -/
@[fun_prop]
lemma measurable_liftBits (ρ : Arm k → α) (τ : ι → Expert k n) : Measurable (liftBits ρ τ) :=
  measurable_of_countable _

/-- The real loss of a loss bit is measurable. -/
@[fun_prop]
lemma measurable_boolLoss : Measurable boolLoss := measurable_of_countable _

/-! ### The reduced strategies -/

/-- The observation kernels of the reduced strategies: uniform advice bits in the first round, and
afterwards the bits of the batch of the arm pulled in the last round are redrawn uniformly. -/
noncomputable def bitsKernel (σ : α → Arm k) :
    (m : ℕ) → Kernel (Hist (Bits k n) α Bool m) (Bits k n)
  | 0 => Kernel.const _ (uniformBits k n)
  | m + 1 => Kernel.ofFunOfCountable fun h ↦
    (uniformBits k n).map (refreshBits (σ (h (Fin.last m)).action) (h (Fin.last m)).obs)

instance (σ : α → Arm k) (m : ℕ) : IsMarkovKernel (bitsKernel (n := n) σ m) := by
  cases m with
  | zero => exact ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (uniformBits k n))⟩
  | succ m =>
    exact ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))⟩

/-- The feedback kernels of the reduced strategy `S_θ`: the law of the loss bit of the pulled
arm given the advice bits of the round. -/
noncomputable def lossBitKernel (σ : α → Arm k) (ε : ℝ) (θ : Expert k n) (m : ℕ) :
    Kernel ((Hist (Bits k n) α Bool m × Bits k n) × α) Bool :=
  Kernel.ofFunOfCountable fun p ↦ (lossRandomness k ε).map (fun r ↦ lossBit θ p.1.2 r (σ p.2))

instance (σ : α → Arm k) (ε : ℝ) (θ : Expert k n) (m : ℕ) :
    IsMarkovKernel (lossBitKernel σ ε θ m) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))⟩

/-- The reduced strategy `S_θ`: an environment with observations the advice bits and feedbacks
the loss bit of the pulled arm. -/
noncomputable def redStrategy (σ : α → Arm k) (ε : ℝ) (θ : Expert k n) :
    Environment (Bits k n) α Bool where
  obs := bitsKernel σ
  feedback := lossBitKernel σ ε θ

/-! ### The strategies with bandit feedback on the general types -/

/-- The law of the loss of an arm given the advice, under `S_θ`. -/
noncomputable def armLossKernel (ε : ℝ) (θ : Expert k n) :
    Kernel ((Expert k n → Arm k) × Arm k) ℝ :=
  Kernel.ofFunOfCountable fun p ↦ (lossLaw ε θ p.1).map (fun ℓ ↦ ℓ p.2)

instance (ε : ℝ) (θ : Expert k n) : IsMarkovKernel (armLossKernel ε θ) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))⟩

/-- The strategy `S_θ` on the general types with bandit feedback: the feedback is the loss of the
pulled arm. -/
noncomputable def banditStrategyOn (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) : Environment (ι → α) α ℝ where
  obs
    | 0 => Kernel.const _ ((initAdvice k n).map (liftAdvice ρ τ))
    | m + 1 => ((adviceKernel k n).comap
        (fun h ↦ (σ (h (Fin.last m)).action, reduceAdvice σ τ' (h (Fin.last m)).obs))
        (by fun_prop)).map (liftAdvice ρ τ)
  feedback _ := (armLossKernel ε θ).comap (fun p ↦ (reduceAdvice σ τ' p.1.2, σ p.2)) (by fun_prop)
  isMarkovKernel_obs m := by
    cases m
    · exact ⟨fun _ ↦ by rw [Kernel.const_apply]; infer_instance⟩
    · exact Kernel.IsMarkovKernel.map _ (measurable_liftAdvice ρ τ)

section KernelApply

variable {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n} {τ' : Expert k n → ι}
  {ε : ℝ} {θ : Expert k n}

omit [Countable α] in
/-- The law of the advice of the round `m + 1` under `strategyOn`. -/
lemma strategyOn_obs_succ_apply (m : ℕ) (h : Hist (ι → α) α (α → ℝ) (m + 1)) :
    (strategyOn σ ρ τ τ' ε θ).obs (m + 1) h = (adviceKernel k n
      (σ (h (Fin.last m)).action, reduceAdvice σ τ' (h (Fin.last m)).obs)).map
        (liftAdvice ρ τ) := by
  simp only [strategyOn]
  rw [Kernel.map_apply _ (measurable_liftAdvice ρ τ), Kernel.comap_apply]

omit [Countable α] in
/-- The law of the losses of a round under `strategyOn`. -/
lemma strategyOn_feedback_apply (m : ℕ) (h : Hist (ι → α) α (α → ℝ) m) (o : ι → α) (a : α) :
    (strategyOn σ ρ τ τ' ε θ).feedback m ((h, o), a) =
      (lossKernel ε θ (reduceAdvice σ τ' o)).map (fun ℓ ↦ ℓ ∘ σ) := by
  simp only [strategyOn]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply]

omit [Countable α] in
/-- The law of the advice of the first round under `banditStrategyOn`. -/
lemma banditStrategyOn_obs_zero_apply (h : Hist (ι → α) α ℝ 0) :
    (banditStrategyOn σ ρ τ τ' ε θ).obs 0 h = (initAdvice k n).map (liftAdvice ρ τ) := by
  simp only [banditStrategyOn, Kernel.const_apply]

omit [Countable α] in
/-- The law of the advice of the round `m + 1` under `banditStrategyOn`. -/
lemma banditStrategyOn_obs_succ_apply (m : ℕ) (h : Hist (ι → α) α ℝ (m + 1)) :
    (banditStrategyOn σ ρ τ τ' ε θ).obs (m + 1) h = (adviceKernel k n
      (σ (h (Fin.last m)).action, reduceAdvice σ τ' (h (Fin.last m)).obs)).map
        (liftAdvice ρ τ) := by
  simp only [banditStrategyOn]
  rw [Kernel.map_apply _ (measurable_liftAdvice ρ τ), Kernel.comap_apply]

omit [Countable α] in
/-- The law of the loss of the pulled arm under `banditStrategyOn`. -/
lemma banditStrategyOn_feedback_apply (m : ℕ) (h : Hist (ι → α) α ℝ m) (o : ι → α) (a : α) :
    (banditStrategyOn σ ρ τ τ' ε θ).feedback m ((h, o), a) =
      (lossLaw ε θ (reduceAdvice σ τ' o)).map (fun ℓ ↦ ℓ (σ a)) := by
  simp only [banditStrategyOn, Kernel.comap_apply]
  rfl

end KernelApply

/-! ### The reduced algorithm -/

/-- The reduced SBI algorithm: it reads advice bits `b` as the advice `liftAdvice ρ τ (adviceOf b)`
and loss bits as losses `0` or `1`. -/
noncomputable def reducedAlg {𝓓 : Type*} [MeasurableSpace 𝓓] (ρ : Arm k → α)
    (τ : ι → Expert k n) (B : IdentAlg (ι → α) α ℝ 𝓓) : IdentAlg (Bits k n) α Bool 𝓓 :=
  B.comapObsFeedback (liftBits ρ τ) boolLoss (measurable_liftBits ρ τ) measurable_boolLoss

/-! ### Transport of the output laws -/

variable {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n} {τ' : Expert k n → ι}

/-- Running an SBI algorithm with bandit feedback against `strategyOn` or against
`banditStrategyOn` gives the same law to its output. -/
lemma outputMeasure_comapBanditFeedback_eq_banditStrategyOn {𝓓 : Type*} [MeasurableSpace 𝓓]
    (B : IdentAlg (ι → α) α ℝ 𝓓) (ε : ℝ) (θ : Expert k n) :
    B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε θ) =
      B.outputMeasure (banditStrategyOn σ ρ τ τ' ε θ) := by
  refine B.outputMeasure_comapPartialFeedback measurable_banditFeedback (fun m h ↦ ?_)
    (fun m h o a ↦ ?_)
  · cases m with
    | zero =>
      simp only [banditStrategyOn_obs_zero_apply, strategyOn, Kernel.const_apply]
    | succ m =>
      rw [strategyOn_obs_succ_apply, banditStrategyOn_obs_succ_apply]
      rfl
  · rw [strategyOn_feedback_apply, banditStrategyOn_feedback_apply]
    change ((lossKernel ε θ (reduceAdvice σ τ' o)).map (fun ℓ ↦ ℓ ∘ σ)).map (fun ℓ ↦ ℓ a) = _
    rw [Measure.map_map (g := fun ℓ : α → ℝ ↦ ℓ a) (f := fun ℓ : Arm k → ℝ ↦ ℓ ∘ σ)
      (measurable_pi_apply a) (measurable_pi_iff.mpr fun a ↦ measurable_pi_apply (σ a))]
    rfl

/-- Running the reduced algorithm against the reduced strategy gives its output the law of the
output of the SBI algorithm against `banditStrategyOn`. -/
lemma outputMeasure_reducedAlg (hσρ : ∀ a, σ (ρ a) = a) (hττ' : ∀ j, τ (τ' j) = j)
    {𝓓 : Type*} [MeasurableSpace 𝓓] (B : IdentAlg (ι → α) α ℝ 𝓓) (ε : ℝ) (θ : Expert k n) :
    (reducedAlg ρ τ B).outputMeasure (redStrategy σ ε θ) =
      B.outputMeasure (banditStrategyOn σ ρ τ τ' ε θ) := by
  refine B.outputMeasure_comapObsFeedback (measurable_liftBits ρ τ) measurable_boolLoss
    (fun m h ↦ ?_) (fun m h o a ↦ ?_)
  · cases m with
    | zero =>
      rw [banditStrategyOn_obs_zero_apply]
      change _ = (uniformBits k n).map (liftBits ρ τ)
      rw [initAdvice, Measure.map_map (measurable_liftAdvice ρ τ) (measurable_of_countable _)]
      rfl
    | succ m =>
      rw [banditStrategyOn_obs_succ_apply]
      change _ = ((uniformBits k n).map
          (refreshBits (σ (h (Fin.last m)).action) (h (Fin.last m)).obs)).map (liftBits ρ τ)
      simp only [Hist.map_apply, Round.action_map, Round.obs_map, id]
      rw [liftBits, reduceAdvice_liftAdvice hσρ hττ', Measure.map_map (measurable_liftBits ρ τ)
        (measurable_of_countable _)]
      change ((uniformBits k n).map _).map (liftAdvice ρ τ) = _
      rw [Measure.map_map (measurable_liftAdvice ρ τ) (measurable_of_countable _)]
      congr 1
  · rw [banditStrategyOn_feedback_apply]
    change _ = ((lossRandomness k ε).map (fun r ↦ lossBit θ o r (σ a))).map boolLoss
    rw [liftBits, reduceAdvice_liftAdvice hσρ hττ', Measure.map_map measurable_boolLoss
      (measurable_of_countable _)]
    change ((lossRandomness k ε).map (lossOf θ (adviceOf o))).map (fun ℓ ↦ ℓ (σ a)) = _
    rw [Measure.map_map (measurable_pi_apply _) (measurable_of_countable _)]
    congr 1
    funext r
    simp

/-- **Reduction to the finite setting.** The output of an SBI algorithm run with bandit feedback
against `strategyOn σ ρ τ τ' ε θ` has the law of the output of the reduced algorithm against the
reduced strategy. -/
lemma outputMeasure_comapBanditFeedback_strategyOn (hσρ : ∀ a, σ (ρ a) = a)
    (hττ' : ∀ j, τ (τ' j) = j) {𝓓 : Type*} [MeasurableSpace 𝓓] (B : IdentAlg (ι → α) α ℝ 𝓓)
    (ε : ℝ) (θ : Expert k n) :
    B.comapBanditFeedback.outputMeasure (strategyOn σ ρ τ τ' ε θ) =
      (reducedAlg ρ τ B).outputMeasure (redStrategy σ ε θ) := by
  rw [outputMeasure_comapBanditFeedback_eq_banditStrategyOn,
    outputMeasure_reducedAlg hσρ hττ']

end Chase2026Tight
