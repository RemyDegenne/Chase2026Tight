/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.LeanMachineLearning.Online.Bandit.ExpertAdvice
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The reduced setting of Chase, Ito, Mehalel (2026), Sections 2 and 3

The lower bound of the paper is proved on a reduced family of instances of the bandit with
expert advice, with `K = 2k + 1` arms and `N = kn + 1` experts:

* arms (`Arm k`): arm `0` and, for each batch `u ∈ [k]`, the two arms `(u, false)`, `(u, true)`;
* experts (`Expert k n`): expert `0`, which always advises arm `0`, and for each batch `u` the
  experts `(u, v)`, `v ∈ [n]`, which advise one of the two arms of batch `u`.

**Advice.** The advice of the experts of batch `u` is a vector of `n` bits, initially uniform.
After a round in which an arm of batch `u` is pulled, the bits of batch `u` are redrawn
uniformly; otherwise they are kept for the next round (`adviceKernel`).

**Losses** (`lossLaw ε θ e`). Losses are in `{0, 1}`; the loss of arm `0` is `Ber(1/2 - ε/2)`;
in every batch `u` exactly one of the two arms is *correct* (has loss `0`). The pool of
strategies is indexed by `θ : Expert k n`: under `S_0` (`θ = 0`) the correct arm of every batch is
uniform; under `S_(u, v)` the arm advised by expert `(u, v)` has loss `Ber(1/2 - ε)` (so it is
correct with probability `1/2 + ε`) and the other batches are as in `S_0`.
`strategy ε θ` is the corresponding adversary, an environment whose observations are the advice
and whose feedbacks are the loss vectors. The *special batch* of `θ` is the batch of the
expert `θ` (`specialBatch θ`, batch `0` for `θ = 0`).

**Special batch identification (SBI).** An algorithm for SBI (`SBIAlg k n`) is an identification
algorithm (`IdentAlg`) in the setting of the bandit with expert advice (bandit feedback), which
stops at some round and outputs a batch. It is *good* (`IsGood ε A'`) if under every strategy of
the pool it outputs the special batch with probability at least `0.95`. `expectedRounds` is the
expected number of rounds it plays before stopping, `T(A', S)` in the paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Finset
open scoped ENNReal ENat

universe u

namespace Chase2026Tight

/-! ### Arms, experts and batches -/

/-- The arms of the reduced setting: arm `0` (`none`) and the two arms `(u, false)`, `(u, true)`
of each batch `u`. -/
def Arm (k : ℕ) := Option (Fin k × Bool)

/-- The experts: expert `0` (`none`) and the experts `(u, v)`, `v ∈ [n]`, of each batch `u`. -/
def Expert (k n : ℕ) := Option (Fin k × Fin n)

/-- The batches: batch `0` (`none`), containing only arm `0` and expert `0`, and the batches
`u ∈ [k]`. -/
def Batch (k : ℕ) := Option (Fin k)

variable {k n : ℕ}

instance : Fintype (Arm k) := inferInstanceAs (Fintype (Option (Fin k × Bool)))
instance : DecidableEq (Arm k) := inferInstanceAs (DecidableEq (Option (Fin k × Bool)))
instance : MeasurableSpace (Arm k) := ⊤
instance : DiscreteMeasurableSpace (Arm k) := ⟨fun _ ↦ trivial⟩

instance : Fintype (Expert k n) := inferInstanceAs (Fintype (Option (Fin k × Fin n)))
instance : DecidableEq (Expert k n) := inferInstanceAs (DecidableEq (Option (Fin k × Fin n)))

instance : Fintype (Batch k) := inferInstanceAs (Fintype (Option (Fin k)))
instance : DecidableEq (Batch k) := inferInstanceAs (DecidableEq (Option (Fin k)))
instance : MeasurableSpace (Batch k) := ⊤
instance : DiscreteMeasurableSpace (Batch k) := ⟨fun _ ↦ trivial⟩

/-- Arm `0`. -/
def Arm.zero : Arm k := none

/-- The arm `(u, b)` of batch `u`. -/
def Arm.ofBatch (u : Fin k) (b : Bool) : Arm k := some (u, b)

/-- The batch of an arm. -/
def Arm.batch (a : Arm k) : Batch k := Option.map Prod.fst (a : Option (Fin k × Bool))

/-- Whether the arm `a` belongs to batch `u`. -/
def Arm.inBatch (a : Arm k) (u : Fin k) : Bool :=
  match (a : Option (Fin k × Bool)) with
  | none => false
  | some (u', _) => decide (u = u')

/-- Expert `0`. -/
def Expert.zero : Expert k n := none

/-- The expert `(u, v)` of batch `u`. -/
def Expert.mk (u : Fin k) (v : Fin n) : Expert k n := some (u, v)

/-- The batch of an expert. -/
def Expert.batch (j : Expert k n) : Batch k := Option.map Prod.fst (j : Option (Fin k × Fin n))

/-- Batch `0`. -/
def Batch.zero : Batch k := none

/-- The special batch of the strategy `S_θ`: the batch of the expert `θ`. -/
def specialBatch (θ : Expert k n) : Batch k := θ.batch

/-! ### The advice process -/

/-- The advice bits: one bit for each expert `(u, v)`. -/
abbrev Bits (k n : ℕ) := Fin k → Fin n → Bool

/-- The advice given by the bits `b`: expert `(u, v)` advises arm `(u, b u v)`, expert `0`
advises arm `0`. -/
def adviceOf (b : Bits k n) : Expert k n → Arm k := fun j ↦
  match (j : Option (Fin k × Fin n)) with
  | none => Arm.zero
  | some (u, v) => Arm.ofBatch u (b u v)

/-- The bits of an advice: the arm advised by expert `(u, v)` is `(u, bitsOf e u v)` (with the
convention `bitsOf e u v = false` if the advice is not an arm of batch `u`). -/
def bitsOf (e : Expert k n → Arm k) : Bits k n := fun u v ↦
  match (e (Expert.mk u v) : Option (Fin k × Bool)) with
  | none => false
  | some (_, b) => b

/-- The uniform law on the advice bits. -/
noncomputable def uniformBits (k n : ℕ) : Measure (Bits k n) :=
  (PMF.uniformOfFintype (Bits k n)).toMeasure

instance : IsProbabilityMeasure (uniformBits k n) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Bits k n)).toMeasure)

/-- The law of the advice of the next round, given the arm `I` pulled and the advice `e` of the
current round: the bits of the batch of `I` are redrawn uniformly, the others are kept. -/
noncomputable def nextAdvice (I : Arm k) (e : Expert k n → Arm k) : Measure (Expert k n → Arm k) :=
  (uniformBits k n).map fun f ↦ adviceOf fun u ↦ if I.inBatch u then f u else bitsOf e u

instance (I : Arm k) (e : Expert k n → Arm k) : IsProbabilityMeasure (nextAdvice I e) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The advice kernel: law of the next advice given the arm pulled and the advice of the current
round. -/
noncomputable def adviceKernel (k n : ℕ) :
    Kernel (Arm k × (Expert k n → Arm k)) (Expert k n → Arm k) :=
  Kernel.ofFunOfCountable fun p ↦ nextAdvice p.1 p.2

instance : IsMarkovKernel (adviceKernel k n) :=
  ⟨fun p ↦ inferInstanceAs (IsProbabilityMeasure (nextAdvice p.1 p.2))⟩

/-! ### The losses -/

/-- The Bernoulli law on `Bool` giving probability `p` to `true` (`p` is clamped to `[0, 1]`). -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

instance (p : ℝ) : IsProbabilityMeasure (bern p) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false _))

/-- The randomness used to draw the losses of a round: a bit `z` (loss of arm `0` is `1` iff
`z`), a uniform bit for each batch (the correct arm of the batch under `S_0`), and a bit `f`
with law `Ber(1/2 - ε)` (under `S_(u, v)`, the arm advised by `(u, v)` is incorrect iff `f`). -/
noncomputable def lossRandomness (k : ℕ) (ε : ℝ) : Measure (Bool × (Fin k → Bool) × Bool) :=
  (bern (1 / 2 - ε / 2)).prod
    (((PMF.uniformOfFintype (Fin k → Bool)).toMeasure).prod (bern (1 / 2 - ε)))

instance (ε : ℝ) : IsProbabilityMeasure (lossRandomness k ε) :=
  inferInstanceAs (IsProbabilityMeasure ((bern (1 / 2 - ε / 2)).prod
    (((PMF.uniformOfFintype (Fin k → Bool)).toMeasure).prod (bern (1 / 2 - ε)))))

/-- The correct arm of batch `u` under `S_θ`, given the advice `e` and the randomness `r`. -/
def correctArm (θ : Expert k n) (e : Expert k n → Arm k) (r : Bool × (Fin k → Bool) × Bool)
    (u : Fin k) : Bool :=
  match (θ : Option (Fin k × Fin n)) with
  | none => r.2.1 u
  | some (u', v) => if u = u' then xor (bitsOf e u' v) r.2.2 else r.2.1 u

/-- The losses of the arms under `S_θ`, given the advice `e` and the randomness `r`: arm `0` has
loss `1` iff `r.1`, and in batch `u` the correct arm has loss `0` and the other arm loss `1`. -/
def lossOf (θ : Expert k n) (e : Expert k n → Arm k) (r : Bool × (Fin k → Bool) × Bool) :
    Arm k → ℝ := fun a ↦
  match (a : Option (Fin k × Bool)) with
  | none => if r.1 then 1 else 0
  | some (u, b) => if b = correctArm θ e r u then 0 else 1

/-- The law of the losses of a round under `S_θ`, given the advice `e`. -/
noncomputable def lossLaw (ε : ℝ) (θ : Expert k n) (e : Expert k n → Arm k) :
    Measure (Arm k → ℝ) :=
  (lossRandomness k ε).map (lossOf θ e)

instance (ε : ℝ) (θ : Expert k n) (e : Expert k n → Arm k) : IsProbabilityMeasure (lossLaw ε θ e) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The loss kernel of `S_θ`: law of the losses given the advice. -/
noncomputable def lossKernel (ε : ℝ) (θ : Expert k n) : Kernel (Expert k n → Arm k) (Arm k → ℝ) :=
  Kernel.ofFunOfCountable (lossLaw ε θ)

instance (ε : ℝ) (θ : Expert k n) : IsMarkovKernel (lossKernel ε θ) :=
  ⟨fun e ↦ inferInstanceAs (IsProbabilityMeasure (lossLaw ε θ e))⟩

/-! ### The strategies -/

/-- The law of the advice of the first round: uniform bits. -/
noncomputable def initAdvice (k n : ℕ) : Measure (Expert k n → Arm k) :=
  (uniformBits k n).map adviceOf

instance : IsProbabilityMeasure (initAdvice k n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The strategy `S_θ` of the adversary (with parameter `ε`), as an environment: the advice
follows the advice process, and the losses of each round are drawn from `lossLaw ε θ` given the
advice of the round. -/
noncomputable def strategy (ε : ℝ) (θ : Expert k n) :
    Environment (Expert k n → Arm k) (Arm k) (Arm k → ℝ) where
  obs
    | 0 => Kernel.const _ (initAdvice k n)
    | m + 1 => (adviceKernel k n).comap
        (fun h ↦ ((h (Fin.last m)).action, (h (Fin.last m)).obs)) (by fun_prop)
  feedback _ := (lossKernel ε θ).comap (fun p ↦ p.1.2) (by fun_prop)
  isMarkovKernel_obs m := by cases m <;> infer_instance

/-- The losses of a round under `S_θ` do not depend on the arm pulled in that round. -/
lemma strategy_feedbackIgnoresAction (ε : ℝ) (θ : Expert k n) :
    (strategy ε θ).FeedbackIgnoresAction :=
  fun _ ↦ ⟨(lossKernel ε θ).comap Prod.snd measurable_snd, rfl⟩

/-- Advice and losses of a round. -/
abbrev AdvLoss (k n : ℕ) := (Expert k n → Arm k) × (Arm k → ℝ)

/-- The law of the advice and losses of a round under `S_θ` when the advice is fresh: the law
of the first round, `P_θ` in the paper. -/
noncomputable def roundLaw (ε : ℝ) (θ : Expert k n) : Measure (AdvLoss k n) :=
  initAdvice k n ⊗ₘ lossKernel ε θ

instance (ε : ℝ) (θ : Expert k n) : IsProbabilityMeasure (roundLaw ε θ) :=
  inferInstanceAs (IsProbabilityMeasure (initAdvice k n ⊗ₘ lossKernel ε θ))

/-! ### Special batch identification -/

/-- An algorithm for special batch identification: an identification algorithm in the setting of
the bandit with expert advice (it chooses responses and observes the advice and the loss of the
pulled arm), which outputs a batch. -/
abbrev SBIAlg (k n : ℕ) := IdentAlg (Expert k n → Arm k) (Arm k) ℝ (Batch k)

/-- An SBI algorithm as an identification algorithm with feedback the loss vector of all arms,
of which it observes only the loss of the pulled arm. -/
noncomputable def SBIAlg.toIdentAlg (A : SBIAlg k n) :
    IdentAlg (Expert k n → Arm k) (Arm k) (Arm k → ℝ) (Batch k) :=
  A.comapBanditFeedback

/-- An SBI algorithm is *good* if under every strategy `S_θ` of the pool, it outputs the special
batch with probability at least `0.95`: its output is another batch with probability at most
`0.05` (LML's `IdentAlg.IsPAC`, on the law of the output). -/
def IsGood (ε : ℝ) (A : SBIAlg k n) : Prop :=
  A.toIdentAlg.IsPAC (fun θ : Expert k n ↦ strategy ε θ) (fun θ b ↦ b ≠ specialBatch θ) 0.05

/-- The expected number of rounds played by the SBI algorithm `A` before stopping, in a run
`(O, X, Y)` (advice, arms, losses) on `(Ω, P)`: `T(A', S)` in the paper. -/
noncomputable def expectedRounds (A : SBIAlg k n) {Ω : Type u} {_ : MeasurableSpace Ω}
    (O : ℕ → Ω → Expert k n → Arm k) (X : ℕ → Ω → Arm k) (Y : ℕ → Ω → Arm k → ℝ)
    (P : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, (A.toIdentAlg.stoppingTime O X Y ω : ℝ≥0∞) ∂P

end Chase2026Tight
