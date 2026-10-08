/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.ReducedRun
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.HistMixture
public import Chase2026Tight.Mathlib.Probability.Distributions.UniformPi

/-!
# Pull records and the tape representation of the runs

Fix a batch `u`. A *pull record* of batch `u` is a pair (advice bits of batch `u`, correct arm of
batch `u`) in `Rec n = (Fin n → Bool) × Bool`. Under `S_0` and `S_(u, v)`, the record of each pull
of batch `u` has the law `recordLaw ε w` (`w = none` for `S_0`, `w = some v` for `S_(u, v)`): the
image of the law of a round of the two-batch game by the projection `recordOf` on the advice bits
and the correct arm (`def:record`).

The advice of batch `u` is redrawn only after a pull of batch `u`, so that the successive records
of the pulls of batch `u` are i.i.d., whatever the algorithm does between the pulls. Formally,
we compare the reduced strategy `redStrategy σ ε θ` with the *tape strategies*
`tapeStrategy σ ε u t`, which read the advice bits and the correct arms of batch `u` at its first
`M` pulls from a tape `t : Fin M → Rec n`, and behave as `S_0` otherwise: along the histories with
at most `M` pulls of batch `u`, the law of the history under `S_θ` is the mixture over a tape with
law `(recordLaw ε w)^M` of its laws under the tape strategies (`lem:record_representation`). For
an algorithm that stops at the latest at its `M`-th pull of batch `u`, the law of the stopped
history is the same mixture (`stoppedHistMeasure_redStrategy_eq_comp`): the tape strategies do
not depend on `θ`, which only enters through the law of the tape.

## Main definitions

* `Rec n`, `recordOf`, `recordLaw ε w`: pull records and their law.
* `tapeStrategy σ ε u t`: the strategy reading batch `u` from the tape `t`.
* `tapeConstr σ u M L h`: the constraints that a history puts on the tape.

## Main statements

* `stoppedHistMeasure_redStrategy_eq_comp`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

variable {k n : ℕ} {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]

/-! ### Records and their law -/

/-- A pull record of a batch: the advice bits of the batch and its correct arm. -/
abbrev Rec (n : ℕ) := (Fin n → Bool) × Bool

/-- The strategy of index `w` relative to batch `u`: `S_0` for `w = none`, `S_(u, v)` for
`w = some v`. -/
def batchExpert (u : Fin k) : Option (Fin n) → Expert k n
  | none => Expert.zero
  | some v => Expert.mk u v

@[simp] lemma batchExpert_none (u : Fin k) : batchExpert (n := n) u none = Expert.zero := rfl

@[simp] lemma batchExpert_some (u : Fin k) (v : Fin n) : batchExpert u (some v) = Expert.mk u v :=
  rfl

/-- The correct arm of the batch of the strategy of index `w`, given the advice bits `β` of the
batch, a uniform bit `c` (used for `w = none`) and a bit `f` (used for `w = some v`: the arm
advised by `v` is correct iff `f` is false). -/
def recBit (w : Option (Fin n)) (β : Fin n → Bool) (c f : Bool) : Bool :=
  match w with
  | none => c
  | some v => xor (β v) f

/-- The correct arm of batch `u` under the strategy of index `w` relative to batch `u`. -/
lemma correctArm_batchExpert_self (u : Fin k) (w : Option (Fin n)) (b : Bits k n)
    (r : Bool × (Fin k → Bool) × Bool) :
    correctArm (batchExpert u w) (adviceOf b) r u = recBit w (b u) (r.2.1 u) r.2.2 := by
  cases w <;> simp [correctArm, batchExpert, Expert.zero, Expert.mk, recBit]

/-- The correct arm of a batch other than `u` does not depend on the strategy of index `w`. -/
lemma correctArm_batchExpert_of_ne {u u' : Fin k} (hu : u' ≠ u) (w : Option (Fin n))
    (e : Expert k n → Arm k) (r : Bool × (Fin k → Bool) × Bool) :
    correctArm (batchExpert u w) e r u' = r.2.1 u' := by
  cases w <;> simp [correctArm, batchExpert, Expert.zero, Expert.mk, hu]

/-- The correct arm of the batch of the two-batch game under the strategy of index `w`. -/
lemma correctArm_batchExpert_zero (w : Option (Fin n)) (e : Expert 1 n → Arm 1)
    (r : Bool × (Fin 1 → Bool) × Bool) :
    correctArm (batchExpert 0 w) e r 0 = recBit w (bitsOf e 0) (r.2.1 0) r.2.2 := by
  cases w <;> simp [correctArm, batchExpert, Expert.zero, Expert.mk, recBit]

/-- The indicator that a real number is zero, as a Boolean, is measurable. -/
private lemma measurable_decide_eq_zero : Measurable (fun x : ℝ ↦ decide (x = 0)) := by
  refine measurable_to_countable' fun b ↦ ?_
  cases b
  · have : (fun x : ℝ ↦ decide (x = 0)) ⁻¹' {false} = {0}ᶜ := by ext; simp
    rw [this]
    exact (measurableSet_singleton 0).compl
  · have : (fun x : ℝ ↦ decide (x = 0)) ⁻¹' {true} = {0} := by ext; simp
    rw [this]
    exact measurableSet_singleton 0

/-- The record of a round of the two-batch game: the advice bits of the batch and its correct arm,
read from the loss of the arm `(0, true)`. -/
noncomputable def recordOf (g : AdvLoss 1 n) : Rec n :=
  (bitsOf g.1 0, decide (g.2 (Arm.ofBatch 0 true) = 0))

/-- The record of a round is a measurable function of the round. -/
@[fun_prop]
lemma measurable_recordOf : Measurable (recordOf (n := n)) :=
  ((measurable_of_countable (fun e : Expert 1 n → Arm 1 ↦ bitsOf e 0)).comp measurable_fst).prodMk
    (measurable_decide_eq_zero.comp ((measurable_pi_apply _).comp measurable_snd))

/-- The law of a pull record under the strategy of index `w`: the image of the law of a round of
the two-batch game. -/
noncomputable def recordLaw (ε : ℝ) (w : Option (Fin n)) : Measure (Rec n) :=
  (roundLaw (k := 1) ε (batchExpert 0 w)).map recordOf

instance (ε : ℝ) (w : Option (Fin n)) : IsProbabilityMeasure (recordLaw ε w) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The probability that the correct arm is `c` given the advice bits `β`, under the strategy of
index `w`. -/
noncomputable def recProb (ε : ℝ) (w : Option (Fin n)) (β : Fin n → Bool) (c : Bool) : ℝ≥0∞ :=
  lossRandomness 1 ε {r | recBit w β (r.2.1 0) r.2.2 = c}

/-- The probability of a correct arm given the advice bits does not depend on the number of
batches nor on the batch. -/
lemma lossRandomness_recBit (k' : ℕ) (u' : Fin k') (ε : ℝ) (w : Option (Fin n))
    (β : Fin n → Bool) (c : Bool) :
    lossRandomness k' ε {r | recBit w β (r.2.1 u') r.2.2 = c} = recProb ε w β c := by
  rw [recProb]
  cases w with
  | none =>
    have h : ∀ (k'' : ℕ) (u'' : Fin k''),
        lossRandomness k'' ε {r | recBit none β (r.2.1 u'') r.2.2 = c} = 2⁻¹ := by
      intro k'' u''
      have : {r : Bool × (Fin k'' → Bool) × Bool | recBit none β (r.2.1 u'') r.2.2 = c} =
          Set.univ ×ˢ ({f : Fin k'' → Bool | f u'' = c} ×ˢ Set.univ) := by
        ext r; simp [recBit]
      rw [this, lossRandomness, Measure.prod_prod, Measure.prod_prod,
        PMF.toMeasure_uniformOfFintype_eval_eq, measure_univ, measure_univ]
      simp
    rw [h, h]
  | some v =>
    have h : ∀ (k'' : ℕ) (u'' : Fin k''),
        lossRandomness k'' ε {r | recBit (some v) β (r.2.1 u'') r.2.2 = c} =
          bern (1 / 2 - ε) {f | xor (β v) f = c} := by
      intro k'' u''
      have : {r : Bool × (Fin k'' → Bool) × Bool | recBit (some v) β (r.2.1 u'') r.2.2 = c} =
          Set.univ ×ˢ (Set.univ ×ˢ {f | xor (β v) f = c}) := by
        ext r; simp [recBit]
      rw [this, lossRandomness, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
        one_mul, one_mul]
    rw [h, h]

/-- In the two-batch game, the arm `(0, true)` has loss `0` iff it is the correct arm. -/
lemma decide_lossOf_ofBatch_true_eq_zero (θ : Expert 1 n) (e : Expert 1 n → Arm 1)
    (r : Bool × (Fin 1 → Bool) × Bool) :
    decide (lossOf θ e r (Arm.ofBatch 0 true) = 0) = correctArm θ e r 0 := by
  simp only [lossOf, Arm.ofBatch]
  rcases Bool.eq_false_or_eq_true (correctArm θ e r 0) with h | h <;> simp [h]

/-- Under the uniform law of the advice bits of the two-batch game, the bits of the batch are
uniform. -/
lemma initAdvice_bitsOf_eq (β : Fin n → Bool) :
    initAdvice 1 n {e | bitsOf e 0 = β} = (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹ := by
  rw [initAdvice, Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  have : adviceOf ⁻¹' {e : Expert 1 n → Arm 1 | bitsOf e 0 = β} = {b : Bits 1 n | b 0 = β} := by
    ext b; simp
  rw [this, uniformBits, PMF.toMeasure_uniformOfFintype_eval_eq]

/-- The advice bits of a record are uniform. -/
lemma recordLaw_fst_eq (ε : ℝ) (w : Option (Fin n)) (β : Fin n → Bool) :
    recordLaw ε w {q | q.1 = β} = (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹ := by
  rw [recordLaw, Measure.map_apply measurable_recordOf (Set.toFinite _).measurableSet]
  have : recordOf ⁻¹' {q : Rec n | q.1 = β} = {e | bitsOf e 0 = β} ×ˢ Set.univ := by
    ext g; simp [recordOf]
  rw [this, roundLaw, Measure.compProd_apply_prod (Set.toFinite _).measurableSet
    MeasurableSet.univ]
  simp only [measure_univ, setLIntegral_const, one_mul]
  exact initAdvice_bitsOf_eq β

/-- The law of a record: uniform advice bits, and the correct arm given the advice bits with
probabilities `recProb ε w`. -/
lemma recordLaw_eq_mul (ε : ℝ) (w : Option (Fin n)) (β : Fin n → Bool) (c : Bool) :
    recordLaw ε w {q | q.1 = β ∧ q.2 = c} =
      (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹ * recProb ε w β c := by
  rw [recordLaw, Measure.map_apply measurable_recordOf (Set.toFinite _).measurableSet]
  have : recordOf ⁻¹' {q : Rec n | q.1 = β ∧ q.2 = c} =
      {e | bitsOf e 0 = β} ×ˢ {ℓ | decide (ℓ (Arm.ofBatch 0 true) = 0) = c} := by
    ext g; simp [recordOf]
  have hmeas : MeasurableSet {ℓ : Arm 1 → ℝ | decide (ℓ (Arm.ofBatch 0 true) = 0) = c} :=
    (measurable_decide_eq_zero.comp (measurable_pi_apply _)) (measurableSet_singleton c)
  rw [this, roundLaw, Measure.compProd_apply_prod (Set.toFinite _).measurableSet hmeas]
  rw [setLIntegral_congr_fun (Set.toFinite _).measurableSet (g := fun _ ↦ recProb ε w β c)]
  · rw [setLIntegral_const, initAdvice_bitsOf_eq, mul_comm]
  · intro e he
    simp only [Set.mem_ofPred_eq] at he
    change lossLaw ε (batchExpert 0 w) e _ = _
    rw [lossLaw, Measure.map_apply (measurable_of_countable _) hmeas, recProb]
    congr 1
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, decide_lossOf_ofBatch_true_eq_zero,
      correctArm_batchExpert_zero, he]

/-! ### Arms of a batch and loss bits -/

/-- The batch `u ∈ [k]`. -/
def Batch.ofFin (u : Fin k) : Batch k := some u

/-- The bit of an arm of a batch (`false` for arm `0`). -/
def armBit (a : Arm k) : Bool :=
  match (a : Option (Fin k × Bool)) with
  | none => false
  | some (_, b) => b

/-- An arm is in batch `u` iff its batch is `u`. -/
private lemma inBatch_eq_true_iff (a : Arm k) (u : Fin k) :
    a.inBatch u = true ↔ a.batch = Batch.ofFin u := by
  rcases a with _ | ⟨u', b⟩
  · simp [Arm.inBatch, Arm.batch, Batch.ofFin]
  · simp only [Arm.inBatch, Arm.batch, Option.map_some, decide_eq_true_eq, Batch.ofFin]
    exact ⟨fun h ↦ by rw [h], fun h ↦ (Option.some.inj h).symm⟩

/-- An arm of batch `u` belongs to no other batch. -/
private lemma inBatch_eq_decide_of_inBatch {a : Arm k} {u : Fin k}
    (ha : a.inBatch u = true) (u' : Fin k) : a.inBatch u' = decide (u' = u) := by
  rcases a with _ | ⟨u'', b⟩
  · simp [Arm.inBatch] at ha
  · simp only [Arm.inBatch, decide_eq_true_eq] at ha ⊢
    rw [ha]

/-- The loss bit of a pulled arm of batch `u` under the strategy of index `w`: the arm has loss
`1` iff it is not the correct arm. -/
lemma lossBit_of_inBatch {u : Fin k} (w : Option (Fin n)) {a : Arm k} (ha : a.inBatch u = true)
    (b : Bits k n) (r : Bool × (Fin k → Bool) × Bool) :
    lossBit (batchExpert u w) b r a = xor (armBit a) (recBit w (b u) (r.2.1 u) r.2.2) := by
  rcases a with _ | ⟨u', b'⟩
  · simp [Arm.inBatch] at ha
  · simp only [Arm.inBatch, decide_eq_true_eq] at ha
    subst ha
    simp only [lossBit, lossOf, armBit, correctArm_batchExpert_self]
    rcases Bool.eq_false_or_eq_true b' with h | h <;>
      rcases Bool.eq_false_or_eq_true (recBit w (b u) (r.2.1 u) r.2.2) with h' | h' <;>
      simp [h, h']

/-- The loss bit of an arm outside of batch `u` does not depend on the strategy of index `w`. -/
lemma lossBit_batchExpert_of_not_inBatch {u : Fin k} (w : Option (Fin n)) {a : Arm k}
    (ha : a.inBatch u = false) (b : Bits k n) (r : Bool × (Fin k → Bool) × Bool) :
    lossBit (batchExpert u w) b r a = lossBit Expert.zero b r a := by
  rcases a with _ | ⟨u', b'⟩
  · rfl
  · simp only [Arm.inBatch, decide_eq_false_iff_not] at ha
    simp only [lossBit, lossOf, correctArm_batchExpert_of_ne (Ne.symm ha)]
    rfl

variable {σ : α → Arm k} {ε : ℝ} {u : Fin k}

/-- The probability of a loss bit of a pulled arm of batch `u` under the strategy of index `w`:
the probability of the correct arm that it reveals, given the advice bits of batch `u`. -/
lemma lossBitKernel_singleton_of_inBatch (w : Option (Fin n)) {m : ℕ}
    (h : Hist (Bits k n) α Bool m) (b : Bits k n) {a : α} (ha : (σ a).inBatch u = true)
    (y : Bool) :
    lossBitKernel σ ε (batchExpert u w) m ((h, b), a) {y} =
      recProb ε w (b u) (xor (armBit (σ a)) y) := by
  change (lossRandomness k ε).map _ {y} = _
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y),
    ← lossRandomness_recBit k u]
  congr 1
  ext r
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    lossBit_of_inBatch w ha]
  rcases Bool.eq_false_or_eq_true (armBit (σ a)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true y with h2 | h2 <;> simp [h1, h2]

/-- The law of the loss bit of an arm outside of batch `u` does not depend on the strategy of
index `w`. -/
lemma lossBitKernel_batchExpert_of_not_inBatch (w : Option (Fin n)) {m : ℕ}
    (h : Hist (Bits k n) α Bool m) (b : Bits k n) {a : α} (ha : (σ a).inBatch u = false) :
    lossBitKernel σ ε (batchExpert u w) m ((h, b), a) =
      lossBitKernel σ ε Expert.zero m ((h, b), a) := by
  change (lossRandomness k ε).map _ = (lossRandomness k ε).map _
  congr 1
  funext r
  exact lossBit_batchExpert_of_not_inBatch w ha b r

/-! ### The tape strategies -/

variable (σ ε u) in
/-- The observation kernels of the tape strategy: as in the reduced strategies, except that at the
`j`-th pull of batch `u` (`j < M`), the advice bits of batch `u` are those of the record `t j`. -/
noncomputable def tapeObsKernel {M : ℕ} (t : Fin M → Rec n) (m : ℕ) :
    Kernel (Hist (Bits k n) α Bool m) (Bits k n) :=
  Kernel.ofFunOfCountable fun h ↦
    if hN : pullCount σ (Batch.ofFin u) h < M then
      (bitsKernel σ m h).map (fun f ↦ Function.update f u (t ⟨_, hN⟩).1)
    else bitsKernel σ m h

instance {M : ℕ} (t : Fin M → Rec n) (m : ℕ) : IsMarkovKernel (tapeObsKernel σ u t m) :=
  ⟨fun h ↦ by
    change IsProbabilityMeasure (dite _ _ _)
    split_ifs
    · exact inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))
    · infer_instance⟩

variable (σ ε u) in
/-- The feedback kernels of the tape strategy: at the `j`-th pull of batch `u` (`j < M`), the
correct arm of batch `u` is that of the record `t j`; otherwise, as under `S_0`. -/
noncomputable def tapeFeedbackKernel {M : ℕ} (t : Fin M → Rec n) (m : ℕ) :
    Kernel ((Hist (Bits k n) α Bool m × Bits k n) × α) Bool :=
  Kernel.ofFunOfCountable fun p ↦
    if hN : (σ p.2).inBatch u = true ∧ pullCount σ (Batch.ofFin u) p.1.1 < M then
      Measure.dirac (xor (armBit (σ p.2)) (t ⟨_, hN.2⟩).2)
    else lossBitKernel σ ε Expert.zero m p

instance {M : ℕ} (t : Fin M → Rec n) (m : ℕ) : IsMarkovKernel (tapeFeedbackKernel σ ε u t m) :=
  ⟨fun p ↦ by
    change IsProbabilityMeasure (dite _ _ _)
    split_ifs <;> infer_instance⟩

variable (σ ε u) in
/-- The tape strategy: batch `u` is read from the tape `t` at its first `M` pulls, the rest is as
under `S_0`. -/
noncomputable def tapeStrategy {M : ℕ} (t : Fin M → Rec n) : Environment (Bits k n) α Bool where
  obs := tapeObsKernel σ u t
  feedback := tapeFeedbackKernel σ ε u t

/-! ### Constraints on the tape -/

variable (σ u) in
/-- The constraint that a round puts on the record of the current pull of batch `u`: its advice
bits are those of batch `u` in the round, and if batch `u` is pulled, its correct arm is revealed
by the loss bit. -/
def roundConstr (r : Round (Bits k n) α Bool) : Set (Rec n) :=
  {q | q.1 = r.obs u ∧ ((σ r.action).inBatch u = true → xor (armBit (σ r.action)) q.2 = r.feedback)}

variable (σ u) in
/-- The constraints that a history puts on the records of the tape: the constraint of each round
applies to the record of the next pull of batch `u` at that round. -/
def tapeConstr (M : ℕ) : (L : ℕ) → Hist (Bits k n) α Bool L → Fin M → Set (Rec n)
  | 0, _ => fun _ ↦ Set.univ
  | L + 1, h => fun j ↦ tapeConstr M L (Fin.init h) j ∩
      (if (j : ℕ) = pullCount σ (Batch.ofFin u) (Fin.init h) then roundConstr σ u (h (Fin.last L))
        else Set.univ)

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The empty history does not constrain the tape. -/
lemma tapeConstr_zero (M : ℕ) (h : Hist (Bits k n) α Bool 0) (j : Fin M) :
    tapeConstr σ u M 0 h j = Set.univ := rfl

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The constraints on the tape after one more round. -/
lemma tapeConstr_snoc (M L : ℕ) (h : Hist (Bits k n) α Bool L) (r : Round (Bits k n) α Bool)
    (j : Fin M) :
    tapeConstr σ u M (L + 1) (Fin.snoc h r) j = tapeConstr σ u M L h j ∩
      (if (j : ℕ) = pullCount σ (Batch.ofFin u) h then roundConstr σ u r else Set.univ) := by
  simp [tapeConstr, Fin.init_snoc, Fin.snoc_last]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The number of pulls of a batch after one more round. -/
private lemma pullCount_snoc {𝓞 𝓨 : Type*} (σ : α → Arm k) (b : Batch k) {L : ℕ}
    (h : Hist 𝓞 α 𝓨 L) (r : Round 𝓞 α 𝓨) :
    pullCount σ b (Fin.snoc h r) = pullCount σ b h + if (σ r.action).batch = b then 1 else 0 := by
  classical
  simp only [pullCount, Finset.card_filter, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The number of pulls of batch `u` after a round in which batch `u` is pulled. -/
private lemma pullCount_snoc_of_inBatch {𝓞 𝓨 : Type*} {L : ℕ} (h : Hist 𝓞 α 𝓨 L)
    {r : Round 𝓞 α 𝓨}
    (hr : (σ r.action).inBatch u = true) :
    pullCount σ (Batch.ofFin u) (Fin.snoc h r) = pullCount σ (Batch.ofFin u) h + 1 := by
  rw [pullCount_snoc, ite_eq_left ((inBatch_eq_true_iff _ _).mp hr)]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The number of pulls of batch `u` after a round in which batch `u` is not pulled. -/
private lemma pullCount_snoc_of_not_inBatch {𝓞 𝓨 : Type*} {L : ℕ} (h : Hist 𝓞 α 𝓨 L)
    {r : Round 𝓞 α 𝓨} (hr : (σ r.action).inBatch u = false) :
    pullCount σ (Batch.ofFin u) (Fin.snoc h r) = pullCount σ (Batch.ofFin u) h := by
  rw [pullCount_snoc, ite_eq_right_iff.mpr, add_zero]
  intro h'
  rw [← inBatch_eq_true_iff, hr] at h'
  exact absurd h' Bool.false_ne_true

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The records after the next pull of batch `u` are not constrained. -/
lemma tapeConstr_of_lt {M L : ℕ} (h : Hist (Bits k n) α Bool L) (j : Fin M)
    (hj : pullCount σ (Batch.ofFin u) h < j) :
    tapeConstr σ u M L h j = Set.univ := by
  induction L with
  | zero => rfl
  | succ L ih =>
    obtain ⟨h, r, rfl⟩ : ∃ h' r, h = Fin.snoc h' r :=
      ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
    rw [tapeConstr_snoc, ih h, ite_eq_right, Set.inter_univ]
    · rw [pullCount_snoc] at hj
      omega
    · rw [pullCount_snoc] at hj
      omega

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- After a pull of batch `u`, the record of the next pull is not constrained. -/
lemma tapeConstr_snoc_of_inBatch {M L : ℕ} (h : Hist (Bits k n) α Bool L)
    {r : Round (Bits k n) α Bool} (hr : (σ r.action).inBatch u = true) (j : Fin M)
    (hj : (j : ℕ) = pullCount σ (Batch.ofFin u) (Fin.snoc h r)) :
    tapeConstr σ u M (L + 1) (Fin.snoc h r) j = Set.univ := by
  rw [pullCount_snoc_of_inBatch h hr] at hj
  rw [tapeConstr_snoc, tapeConstr_of_lt h j (by omega), ite_eq_right (by omega), Set.inter_univ]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- Before a pull of batch `u`, the record of the next pull is constrained by its advice bits
only. -/
lemma tapeConstr_snoc_of_not_inBatch {M L : ℕ} (h : Hist (Bits k n) α Bool L)
    {r : Round (Bits k n) α Bool} (hr : (σ r.action).inBatch u = false) (j : Fin M)
    (hj : (j : ℕ) = pullCount σ (Batch.ofFin u) (Fin.snoc h r)) :
    tapeConstr σ u M (L + 1) (Fin.snoc h r) j = ∅ ∨
      tapeConstr σ u M (L + 1) (Fin.snoc h r) j = {q | q.1 = r.obs u} := by
  induction L generalizing r j with
  | zero =>
    rw [pullCount_snoc_of_not_inBatch h hr] at hj
    have h_round : roundConstr σ u r = {q | q.1 = r.obs u} := by
      ext q; simp [roundConstr, hr]
    right
    rw [tapeConstr_snoc, ite_eq_left hj, h_round, tapeConstr_zero, Set.univ_inter]
  | succ L ih =>
    rw [pullCount_snoc_of_not_inBatch h hr] at hj
    have h_round : roundConstr σ u r = {q | q.1 = r.obs u} := by
      ext q; simp [roundConstr, hr]
    rw [tapeConstr_snoc, ite_eq_left hj, h_round]
    obtain ⟨h, r', rfl⟩ : ∃ h' r', h = Fin.snoc h' r' :=
      ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
    rcases Bool.eq_false_or_eq_true ((σ r'.action).inBatch u) with hr' | hr'
    · rw [tapeConstr_snoc_of_inBatch h hr' j hj, Set.univ_inter]
      right; rfl
    · rcases ih h hr' j hj with h0 | h0
      · left; rw [h0, Set.empty_inter]
      · rw [h0]
        by_cases hobs : r'.obs u = r.obs u
        · right
          rw [hobs, Set.inter_self]
        · left
          ext q
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          intro h1 h2
          exact hobs (h1.symm.trans h2)

/-! ### Step probabilities -/

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- A function updated at `i` with `x` is `o` iff `x = o i` and the update with `o i` is `o`. -/
private lemma update_eq_iff {ι β : Type*} [DecidableEq ι] (g o : ι → β) (i : ι) (x : β) :
    Function.update g i x = o ↔ x = o i ∧ Function.update g i (o i) = o := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, h⟩
    exact h

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- A function is `o` iff its update at `i` with `o i` is `o` and its value at `i` is `o i`. -/
private lemma eq_iff_update_eq {ι β : Type*} [DecidableEq ι] (g o : ι → β) (i : ι) :
    g = o ↔ Function.update g i (o i) = o ∧ g i = o i := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1, h2⟩
    rw [← h2, Function.update_eq_self] at h1
    exact h1

/-- The law of the advice bits after the round `r`: the batch of the pulled arm is redrawn. -/
lemma bitsKernel_succ_apply (m : ℕ) (h : Hist (Bits k n) α Bool m)
    (r : Round (Bits k n) α Bool) :
    bitsKernel σ (m + 1) (Fin.snoc h r) =
      (uniformBits k n).map (refreshBits (σ r.action) r.obs) := by
  simp only [bitsKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, Fin.snoc_last]

/-- After a pull of batch `u`, only the bits of batch `u` are redrawn. -/
lemma refreshBits_of_inBatch {I : Arm k} (hI : I.inBatch u = true) (b f : Bits k n) :
    refreshBits I b f = Function.update b u (f u) := by
  funext u'
  simp only [refreshBits, inBatch_eq_decide_of_inBatch hI u']
  by_cases hu : u' = u
  · subst hu; simp
  · simp [hu]

/-- After a round in which batch `u` is not pulled, the bits of batch `u` are kept. -/
lemma refreshBits_apply_of_not_inBatch {I : Arm k} (hI : I.inBatch u = false) (b f : Bits k n) :
    refreshBits I b f u = b u := by
  simp [refreshBits, hI]

/-- **Advice bits and the record of batch `u`.** The probability of the advice bits `o` given a
history, times the probability of the constraint on the record of the next pull of batch `u`, is
the probability of the advice bits of the other batches times the probability of the constraint
completed by the advice bits of batch `u`. -/
lemma bitsKernel_singleton_mul (w : Option (Fin n)) {M L : ℕ} (h : Hist (Bits k n) α Bool L)
    (o : Bits k n) (j : Fin M) (hj : (j : ℕ) = pullCount σ (Batch.ofFin u) h) :
    bitsKernel σ L h {o} * recordLaw ε w (tapeConstr σ u M L h j) =
      bitsKernel σ L h {f | Function.update f u (o u) = o} *
        recordLaw ε w (tapeConstr σ u M L h j ∩ {q | q.1 = o u}) := by
  cases L with
  | zero =>
    simp only [tapeConstr_zero, measure_univ, mul_one, Set.univ_inter, recordLaw_fst_eq]
    exact PMF.toMeasure_uniformOfFintype_singleton_eq_mul u o
  | succ L =>
    obtain ⟨h, r, rfl⟩ : ∃ h' r, h = Fin.snoc h' r :=
      ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
    rw [bitsKernel_succ_apply, Measure.map_apply (measurable_of_countable _)
        (measurableSet_singleton _),
      Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
    rcases Bool.eq_false_or_eq_true ((σ r.action).inBatch u) with hI | hI
    · rw [tapeConstr_snoc_of_inBatch h hI j hj, measure_univ, mul_one, Set.univ_inter,
        recordLaw_fst_eq]
      have h1 : (refreshBits (σ r.action) r.obs) ⁻¹' {o} =
          {f | Function.update r.obs u (f u) = o} := by
        ext f; simp [refreshBits_of_inBatch hI]
      have h2 : (refreshBits (σ r.action) r.obs) ⁻¹' {f | Function.update f u (o u) = o} =
          {_f | Function.update r.obs u (o u) = o} := by
        ext f; simp [refreshBits_of_inBatch hI]
      rw [h1, h2]
      by_cases hP : Function.update r.obs u (o u) = o
      · have h3 : {f : Bits k n | Function.update r.obs u (f u) = o} = {f | f u = o u} := by
          ext f
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, update_eq_iff]
          exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hP⟩⟩
        simp only [hP, Set.ofPred_true, measure_univ, one_mul, h3]
        exact PMF.toMeasure_uniformOfFintype_eval_eq u (o u)
      · have h3 : {f : Bits k n | Function.update r.obs u (f u) = o} = ∅ := by
          ext f
          rw [Set.mem_ofPred_eq, update_eq_iff]
          simp [hP]
        simp [hP, h3]
    · have h_pre : (refreshBits (σ r.action) r.obs) ⁻¹' {o} =
          (refreshBits (σ r.action) r.obs) ⁻¹' {f | Function.update f u (o u) = o} ∩
            {_f | r.obs u = o u} := by
        ext f
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
        rw [eq_iff_update_eq _ o u, refreshBits_apply_of_not_inBatch hI]
      rw [h_pre]
      by_cases hb : r.obs u = o u
      · simp only [hb, Set.ofPred_true, Set.inter_univ]
        congr 1
        rcases tapeConstr_snoc_of_not_inBatch h hI j hj with h0 | h0 <;> rw [h0]
        · simp
        · rw [hb, Set.inter_self]
      · simp only [hb, Set.ofPred_false, Set.inter_empty, measure_empty, zero_mul]
        rcases tapeConstr_snoc_of_not_inBatch h hI j hj with h0 | h0 <;> rw [h0]
        · simp
        · have : {q : Rec n | q.1 = r.obs u} ∩ {q | q.1 = o u} = ∅ := by
            ext q
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
              not_and]
            intro h1 h2
            exact hb (h1.symm.trans h2)
          rw [this, measure_empty, mul_zero]

/-- **Loss bits and the record of batch `u`.** The probability of the loss bit `y` given the
advice bits `o` and the arm `a`, times the probability of the constraint `B` on the record of
the current pull of batch `u` (no constraint, or advice bits of batch `u` given by `o`), is the
probability of the constraint completed by the correct arm revealed by `y` if `a` is in
batch `u`, and is the probability under `S_0` of the loss bit otherwise. -/
lemma lossBitKernel_singleton_mul (w : Option (Fin n)) {L : ℕ} (h : Hist (Bits k n) α Bool L)
    (o : Bits k n) (a : α) (y : Bool) (B : Set (Rec n)) (hB : B = ∅ ∨ B = {q | q.1 = o u}) :
    lossBitKernel σ ε (batchExpert u w) L ((h, o), a) {y} * recordLaw ε w B =
      (if (σ a).inBatch u = true then 1 else lossBitKernel σ ε Expert.zero L ((h, o), a) {y}) *
        recordLaw ε w (B ∩ {q | (σ a).inBatch u = true → xor (armBit (σ a)) q.2 = y}) := by
  rcases hB with rfl | rfl
  · simp
  rcases Bool.eq_false_or_eq_true ((σ a).inBatch u) with ha | ha
  · rw [lossBitKernel_singleton_of_inBatch w h o ha y, ite_eq_left ha, one_mul,
      recordLaw_fst_eq]
    have : {q : Rec n | q.1 = o u} ∩ {q | (σ a).inBatch u = true → xor (armBit (σ a)) q.2 = y} =
        {q | q.1 = o u ∧ q.2 = xor (armBit (σ a)) y} := by
      ext q
      simp only [ha, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
      rcases Bool.eq_false_or_eq_true (armBit (σ a)) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true y with h2 | h2 <;>
        rcases Bool.eq_false_or_eq_true q.2 with h3 | h3 <;> simp [h1, h2, h3]
    rw [this, recordLaw_eq_mul, mul_comm]
  · rw [lossBitKernel_batchExpert_of_not_inBatch w h o ha, ite_eq_right (by simp [ha])]
    congr 2
    ext q
    simp [ha]

/-! ### Step probabilities of the tape strategies -/

/-- The probability of advice bits under a tape strategy before the `M`-th pull of batch `u`:
the bits of batch `u` are those of the tape. -/
lemma tapeObsKernel_singleton_of_lt {M L : ℕ} (t : Fin M → Rec n) (h : Hist (Bits k n) α Bool L)
    (hN : pullCount σ (Batch.ofFin u) h < M) (o : Bits k n) :
    tapeObsKernel σ u t L h {o} = if (t ⟨_, hN⟩).1 = o u then
      bitsKernel σ L h {f | Function.update f u (o u) = o} else 0 := by
  change (dite _ _ _ : Measure (Bits k n)) {o} = _
  rw [dite_eq_left hN, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  split_ifs with hx
  · congr 1
    ext f
    simp [hx]
  · have : (fun f : Bits k n ↦ Function.update f u (t ⟨_, hN⟩).1) ⁻¹' {o} = ∅ := by
      ext f
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h'
      apply hx
      rw [← h', Function.update_self]
    rw [this, measure_empty]

/-- After `M` pulls of batch `u`, the advice bits of a tape strategy are those of `S_0`. -/
lemma tapeObsKernel_of_not_lt {M L : ℕ} (t : Fin M → Rec n) (h : Hist (Bits k n) α Bool L)
    (hN : ¬ pullCount σ (Batch.ofFin u) h < M) :
    tapeObsKernel σ u t L h = bitsKernel σ L h := by
  change (dite _ _ _ : Measure (Bits k n)) = _
  rw [dite_eq_right hN]

/-- The probability of a loss bit under a tape strategy before the `M`-th pull of batch `u`:
the correct arm of batch `u` is that of the tape. -/
lemma tapeFeedbackKernel_singleton_of_lt {M L : ℕ} (t : Fin M → Rec n)
    (h : Hist (Bits k n) α Bool L) (hN : pullCount σ (Batch.ofFin u) h < M) (o : Bits k n)
    (a : α) (y : Bool) :
    tapeFeedbackKernel σ ε u t L ((h, o), a) {y} = if (σ a).inBatch u = true then
      (if xor (armBit (σ a)) (t ⟨_, hN⟩).2 = y then 1 else 0)
      else lossBitKernel σ ε Expert.zero L ((h, o), a) {y} := by
  change (dite _ _ _ : Measure Bool) {y} = _
  by_cases ha : (σ a).inBatch u = true
  · rw [dite_eq_left ⟨ha, hN⟩, ite_eq_left ha, Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp only [Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
  · rw [dite_eq_right (fun h' ↦ ha h'.1), ite_eq_right ha]

/-- After `M` pulls of batch `u`, the loss bits of a tape strategy are those of `S_0`. -/
lemma tapeFeedbackKernel_of_not_lt {M L : ℕ} (t : Fin M → Rec n) (h : Hist (Bits k n) α Bool L)
    (hN : ¬ pullCount σ (Batch.ofFin u) h < M) (o : Bits k n) (a : α) :
    tapeFeedbackKernel σ ε u t L ((h, o), a) = lossBitKernel σ ε Expert.zero L ((h, o), a) := by
  change (dite _ _ _ : Measure Bool) = _
  rw [dite_eq_right (fun h' ↦ hN h'.2)]

/-! ### The constraints on the tape as boxes -/

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The constraint on the record of the next pull of batch `u`, completed by advice bits `β` of
batch `u`, is either empty or the set of records with advice bits `β`. -/
lemma tapeConstr_inter_eq {M L : ℕ} (h : Hist (Bits k n) α Bool L) (j : Fin M)
    (hj : (j : ℕ) = pullCount σ (Batch.ofFin u) h) (β : Fin n → Bool) :
    tapeConstr σ u M L h j ∩ {q | q.1 = β} = ∅ ∨
      tapeConstr σ u M L h j ∩ {q | q.1 = β} = {q | q.1 = β} := by
  cases L with
  | zero => right; rw [tapeConstr_zero, Set.univ_inter]
  | succ L =>
    obtain ⟨h, r, rfl⟩ : ∃ h' r, h = Fin.snoc h' r :=
      ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
    rcases Bool.eq_false_or_eq_true ((σ r.action).inBatch u) with hI | hI
    · right; rw [tapeConstr_snoc_of_inBatch h hI j hj, Set.univ_inter]
    · rcases tapeConstr_snoc_of_not_inBatch h hI j hj with h0 | h0 <;> rw [h0]
      · left; rw [Set.empty_inter]
      · by_cases hb : r.obs u = β
        · right; rw [hb, Set.inter_self]
        · left
          ext q
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          intro h1 h2
          exact hb (h1.symm.trans h2)

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- A tape satisfies the constraints of a history extended by a round before the `M`-th pull of
batch `u` iff it satisfies those of the history and the constraint of the round on the record
of the next pull. -/
lemma mem_pi_tapeConstr_snoc_iff {M L : ℕ} (h : Hist (Bits k n) α Bool L)
    (r : Round (Bits k n) α Bool) (hN : pullCount σ (Batch.ofFin u) h < M) (t : Fin M → Rec n) :
    t ∈ Set.univ.pi (tapeConstr σ u M (L + 1) (Fin.snoc h r)) ↔
      t ∈ Set.univ.pi (tapeConstr σ u M L h) ∧ t ⟨_, hN⟩ ∈ roundConstr σ u r := by
  simp only [Set.mem_univ_pi, tapeConstr_snoc, Set.mem_inter_iff]
  constructor
  · intro H
    refine ⟨fun j ↦ (H j).1, ?_⟩
    have := (H ⟨_, hN⟩).2
    rwa [ite_eq_left rfl] at this
  · rintro ⟨H1, H2⟩ j
    refine ⟨H1 j, ?_⟩
    split_ifs with hj
    · have : j = ⟨_, hN⟩ := Fin.ext hj
      subst this
      exact H2
    · trivial

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- After `M` pulls of batch `u`, the rounds do not constrain the tape. -/
lemma pi_tapeConstr_snoc_of_not_lt {M L : ℕ} (h : Hist (Bits k n) α Bool L)
    (r : Round (Bits k n) α Bool) (hN : ¬ pullCount σ (Batch.ofFin u) h < M) :
    Set.univ.pi (tapeConstr σ u M (L + 1) (Fin.snoc h r)) =
      Set.univ.pi (tapeConstr σ u M L h) := by
  congr 1
  funext j
  rw [tapeConstr_snoc, ite_eq_right (by omega), Set.inter_univ]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The probability of the constraints of a history, split at the record of the next pull of
batch `u`. -/
lemma measure_pi_tapeConstr {M L : ℕ} (μ : Measure (Rec n)) [IsProbabilityMeasure μ]
    (h : Hist (Bits k n) α Bool L) (hN : pullCount σ (Batch.ofFin u) h < M) :
    Measure.pi (fun _ : Fin M ↦ μ) (Set.univ.pi (tapeConstr σ u M L h)) =
      μ (tapeConstr σ u M L h ⟨_, hN⟩) *
        ∏ j ∈ ({⟨_, hN⟩} : Finset (Fin M))ᶜ, μ (tapeConstr σ u M L h j) := by
  rw [Measure.pi_pi, Fintype.prod_eq_mul_prod_compl ⟨_, hN⟩]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- The probability of the constraints of a history extended by a round, split at the record of
the next pull of batch `u`. -/
lemma measure_pi_tapeConstr_snoc {M L : ℕ} (μ : Measure (Rec n)) [IsProbabilityMeasure μ]
    (h : Hist (Bits k n) α Bool L) (r : Round (Bits k n) α Bool)
    (hN : pullCount σ (Batch.ofFin u) h < M) :
    Measure.pi (fun _ : Fin M ↦ μ) (Set.univ.pi (tapeConstr σ u M (L + 1) (Fin.snoc h r))) =
      μ (tapeConstr σ u M L h ⟨_, hN⟩ ∩ roundConstr σ u r) *
        ∏ j ∈ ({⟨_, hN⟩} : Finset (Fin M))ᶜ, μ (tapeConstr σ u M L h j) := by
  rw [Measure.pi_pi, Fintype.prod_eq_mul_prod_compl ⟨_, hN⟩, tapeConstr_snoc, ite_eq_left rfl]
  congr 1
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have hj' : (j : ℕ) ≠ pullCount σ (Batch.ofFin u) h := by
    intro h'
    simp only [Finset.mem_compl, Finset.mem_singleton] at hj
    exact hj (Fin.ext h')
  rw [tapeConstr_snoc, ite_eq_right hj', Set.inter_univ]

/-! ### The mixture representation -/

variable (σ ε u) in
/-- The factor of the step probabilities common to the reduced strategy and to the tape
strategies, along the histories with at most `M` pulls of batch `u`. -/
noncomputable def tapeFactor (alg : Algorithm (Bits k n) α Bool) (M L : ℕ)
    (h : Hist (Bits k n) α Bool L) (r : Round (Bits k n) α Bool) : ℝ≥0∞ :=
  if pullCount σ (Batch.ofFin u) h < M then
    bitsKernel σ L h {f | Function.update f u (r.obs u) = r.obs} *
      alg.policy L (h, r.obs) {r.action} *
      (if (σ r.action).inBatch u = true then 1
        else lossBitKernel σ ε Expert.zero L ((h, r.obs), r.action) {r.feedback})
  else stepKernel alg (redStrategy σ ε Expert.zero) L h {r}

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- An identity of products used to combine the observation and feedback steps. -/
private lemma mul_eq_of_mul_eq_of_mul_eq {Bo P F A R gO A' gY A'' : ℝ≥0∞}
    (h1 : Bo * A = gO * A') (h2 : F * A' = gY * A'') :
    Bo * P * F * (A * R) = gO * P * gY * (A'' * R) := by
  calc Bo * P * F * (A * R) = P * F * (Bo * A) * R := by ring
  _ = P * F * (gO * A') * R := by rw [h1]
  _ = gO * P * (F * A') * R := by ring
  _ = gO * P * (gY * A'') * R := by rw [h2]
  _ = gO * P * gY * (A'' * R) := by ring

/-- **Record representation** (`lem:record_representation`). For an algorithm in the reduced
setting whose stopping rule `S` stops at the latest at the `M`-th pull of batch `u`, the law of
the history stopped by `S` under the strategy of index `w` (`S_0` or `S_(u, v)`) is the mixture,
over a tape of `M` i.i.d. records with law `recordLaw ε w`, of its laws under the tape strategies,
which do not depend on `w`. -/
lemma stoppedHistMeasure_redStrategy_eq_comp (w : Option (Fin n)) (M : ℕ)
    (alg : Algorithm (Bits k n) α Bool) {S : Set (Σ m, Hist (Bits k n) α Bool m)}
    (hS : MeasurableSet S)
    (hSM : ∀ m (h : Hist (Bits k n) α Bool m), M ≤ pullCount σ (Batch.ofFin u) h →
      (⟨m, h⟩ : Σ m, Hist (Bits k n) α Bool m) ∈ S) :
    stoppedHistMeasure alg (redStrategy σ ε (batchExpert u w)) S =
      stoppedHistKernel alg (tapeStrategy σ ε u (M := M)) S ∘ₘ
        Measure.pi (fun _ : Fin M ↦ recordLaw ε w) := by
  refine stoppedHistMeasure_eq_comp_of_factor hS
    (D := fun L ↦ {h | pullCount σ (Batch.ofFin u) h ≤ M})
    (C := fun L h ↦ Set.univ.pi (tapeConstr σ u M L h)) (g := tapeFactor σ ε u alg M)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- the histories with at most `M` pulls of batch `u` are closed under prefixes
    intro L h r hr
    simp only [Set.mem_ofPred_eq] at hr ⊢
    rw [pullCount_snoc] at hr
    omega
  · intro h
    ext t
    simp [tapeConstr_zero]
  · intro L h r
    exact Set.pi_mono fun j _ ↦ by rw [tapeConstr_snoc]; exact Set.inter_subset_left
  · -- the step probabilities of the tape strategies
    classical
    rintro L h ⟨o, a, y⟩ hD t ht
    rw [stepKernel_singleton]
    change tapeObsKernel σ u t L h {o} * alg.policy L (h, o) {a} *
      tapeFeedbackKernel σ ε u t L ((h, o), a) {y} = _
    by_cases hN : pullCount σ (Batch.ofFin u) h < M
    · rw [tapeObsKernel_singleton_of_lt t h hN, tapeFeedbackKernel_singleton_of_lt t h hN,
        tapeFactor, ite_eq_left hN]
      have hind : (Set.univ.pi (tapeConstr σ u M (L + 1) (Fin.snoc h (o, a, y)))).indicator 1 t =
          if t ⟨_, hN⟩ ∈ roundConstr σ u (o, a, y) then (1 : ℝ≥0∞) else 0 := by
        simp only [Set.indicator, mem_pi_tapeConstr_snoc_iff h _ hN, ht, true_and, Pi.one_apply]
      rw [hind]
      simp only [roundConstr, Set.mem_ofPred_eq, Round.obs, Round.action, Round.feedback]
      by_cases h1 : (t ⟨_, hN⟩).1 = o u <;> by_cases h2 : (σ a).inBatch u = true <;>
        simp [h1, h2]
    · rw [tapeObsKernel_of_not_lt t h hN, tapeFeedbackKernel_of_not_lt t h hN, tapeFactor,
        ite_eq_right hN, pi_tapeConstr_snoc_of_not_lt h _ hN, Set.indicator_of_mem ht, Pi.one_apply,
        mul_one, stepKernel_singleton]
      rfl
  · -- the step probabilities of the reduced strategy
    rintro L h ⟨o, a, y⟩ hD
    rw [stepKernel_singleton]
    change bitsKernel σ L h {o} * alg.policy L (h, o) {a} *
      lossBitKernel σ ε (batchExpert u w) L ((h, o), a) {y} * _ = _
    by_cases hN : pullCount σ (Batch.ofFin u) h < M
    · rw [measure_pi_tapeConstr _ h hN, measure_pi_tapeConstr_snoc _ h _ hN, tapeFactor,
        ite_eq_left hN]
      have hobs := bitsKernel_singleton_mul (σ := σ) (u := u) (ε := ε) w h o ⟨_, hN⟩ rfl
      have hfb := lossBitKernel_singleton_mul (σ := σ) (ε := ε) w h o a y _
        (tapeConstr_inter_eq h ⟨_, hN⟩ rfl (o u))
      have hround : tapeConstr σ u M L h ⟨_, hN⟩ ∩ roundConstr σ u (o, a, y) =
          tapeConstr σ u M L h ⟨_, hN⟩ ∩ {q | q.1 = o u} ∩
            {q | (σ a).inBatch u = true → xor (armBit (σ a)) q.2 = y} := by
        ext q
        simp [roundConstr, and_assoc]
      simp only [Round.obs, Round.action, Round.feedback] at hround ⊢
      rw [hround]
      exact mul_eq_of_mul_eq_of_mul_eq hobs hfb
    · have ha : (σ a).inBatch u = false := by
        rcases Bool.eq_false_or_eq_true ((σ a).inBatch u) with ha | ha
        · simp only [Set.mem_ofPred_eq] at hD
          rw [pullCount_snoc_of_inBatch h ha] at hD
          omega
        · exact ha
      rw [pi_tapeConstr_snoc_of_not_lt h _ hN, tapeFactor, ite_eq_right hN, stepKernel_singleton,
        lossBitKernel_batchExpert_of_not_inBatch w h o ha]
      rfl
  · -- the histories along which the algorithm has not stopped have at most `M` pulls
    intro L h hh
    simp only [Set.mem_ofPred_eq]
    cases L with
    | zero => simp [pullCount]
    | succ L =>
      obtain ⟨h, r, rfl⟩ : ∃ h' r, h = Fin.snoc h' r :=
        ⟨Fin.init h, h (Fin.last L), (Fin.snoc_init_self h).symm⟩
      have h1 := hh L (Nat.lt_succ_self L)
      have h2 : (fun i : Fin L ↦ (Fin.snoc h r : Hist (Bits k n) α Bool (L + 1))
          (Fin.castLE (Nat.lt_succ_self L).le i)) = h := by
        funext i
        exact Fin.snoc_castSucc (α := fun _ ↦ Round (Bits k n) α Bool) _ _ _
      rw [h2] at h1
      have h3 : pullCount σ (Batch.ofFin u) h < M := by
        by_contra h'
        exact h1 (hSM L h (not_lt.mp h'))
      rw [pullCount_snoc]
      split_ifs <;> omega

end Chase2026Tight
