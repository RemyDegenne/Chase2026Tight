/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting
public import Chase2026Tight.Mathlib.MeasureTheory.Measure.WithDensity
public import Chase2026Tight.Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# The law of a round of the two-batch game as a measure with density

In the two-batch game (`k = 1`), the law `P_(1, v) = roundLaw ε (Expert.mk 0 v)` of the advice and
losses of a round under `S_(1, v)` has density `roundDensity ε v` with respect to
`P_0 = roundLaw ε Expert.zero`: `1 + 2ε` if the arm advised by the expert `(1, v)` has loss `0`
(it is the correct arm of batch `1`), and `1 - 2ε` otherwise. Under `P_0`, the bits of two
distinct experts and the correct arm are independent uniform bits; under `P_(1, v)`, the arm
advised by `(1, v)` is correct with probability `1/2 + ε`. Hence the expectation of the likelihood
ratio of `(1, v)` under `P_(1, w)` is `1 + 4ε²` if `v = w` and `1` otherwise.

## Main definitions

* `roundDensity ε v`: the density of `roundLaw ε (Expert.mk 0 v)` with respect to
  `roundLaw ε Expert.zero`, `f_v` in the paper.

## Main statements

* `roundLaw_mk_eq_withDensity`: `roundLaw ε (Expert.mk 0 v)` is
  `(roundLaw ε Expert.zero).withDensity (roundDensity ε v)`.
* `lintegral_roundDensity`: `∫ f_v dP_(1, w)` is `1 + 4ε²` if `v = w` and `1` otherwise.
* `lintegral_prod_roundDensity`: `∫ ∏_t f_v(g_t) dP_(1, w)^T` is `(1 + 4ε²)^T` if `v = w` and `1`
  otherwise.

## Implementation notes

Under both strategies, the loss vector of a round is `lossVec z c`, a function of the bit `z`
(arm `0` has loss `1` iff `z`) and of the correct arm `(1, c)` of batch `1`. The laws of `(z, c)`
given the advice are measures on the finite type `Bool × Bool`, computed point by point.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

variable {n : ℕ} {ε : ℝ}

/-! ### Bernoulli and uniform laws -/

/-- `bern p` gives mass `p` to `true` for `p ∈ [0, 1]`. -/
lemma bern_singleton_true {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    bern p {true} = ENNReal.ofReal p := by
  rw [bern, bernoulliMeasure_apply _ (measurableSet_singleton _), Set.projIcc_of_mem _ ⟨h0, h1⟩]
  simp only [Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte]
  rw [ENNReal.ofReal_eq_coe_nnreal h0]
  rfl

/-- `bern p` gives mass `1 - p` to `false` for `p ∈ [0, 1]`. -/
lemma bern_singleton_false {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    bern p {false} = ENNReal.ofReal (1 - p) := by
  rw [bern, bernoulliMeasure_apply _ (measurableSet_singleton _), Set.projIcc_of_mem _ ⟨h0, h1⟩]
  simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte]
  rw [ENNReal.ofReal_eq_coe_nnreal (by linarith)]
  rfl

/-- `x / 2` in `ℝ≥0∞` as `ofReal`. -/
private lemma ofReal_mul_inv_two {x : ℝ} : ENNReal.ofReal x * 2⁻¹ = ENNReal.ofReal (x / 2) := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- `(1 + 2ε) + (1 - 2ε) = 2` in `ℝ≥0∞`, for `|ε| ≤ 1/2`. -/
private lemma ofReal_one_add_add_ofReal_one_sub (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    ENNReal.ofReal (1 + 2 * ε) + ENNReal.ofReal (1 - 2 * ε) = 2 := by
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_ofNat 2]
  congr 1
  ring

/-! ### The losses of a round as a function of two bits -/

/-- The loss vector of a round of the two-batch game in which arm `0` has loss `1` iff `z` and the
correct arm of batch `1` is `(1, c)`. -/
def lossVec (z c : Bool) : Arm 1 → ℝ := fun a ↦
  match (a : Option (Fin 1 × Bool)) with
  | none => if z then 1 else 0
  | some (_, b) => if b = c then 0 else 1

/-- `lossVec` is measurable (its domain is finite). -/
lemma measurable_lossVec : Measurable (Function.uncurry lossVec) := measurable_of_countable _

/-- Under `S_0`, the correct arm of batch `1` is the uniform bit of the loss randomness. -/
lemma lossOf_zero_eq (e : Expert 1 n → Arm 1) (r : Bool × (Fin 1 → Bool) × Bool) :
    lossOf Expert.zero e r = lossVec r.1 (r.2.1 0) := by
  funext a
  rcases a with _ | ⟨u, b⟩
  · rfl
  · obtain rfl : u = 0 := Subsingleton.elim _ _
    simp only [lossOf, lossVec, correctArm, Expert.zero]
    congr

/-- Under `S_(1, v)`, the correct arm of batch `1` is the bit of the expert `(1, v)`, flipped iff
the `Ber(1/2 - ε)` bit of the loss randomness is `true`. -/
lemma lossOf_mk_eq (v : Fin n) (e : Expert 1 n → Arm 1) (r : Bool × (Fin 1 → Bool) × Bool) :
    lossOf (Expert.mk 0 v) e r = lossVec r.1 (xor (bitsOf e 0 v) r.2.2) := by
  funext a
  rcases a with _ | ⟨u, b⟩
  · rfl
  · obtain rfl : u = 0 := Subsingleton.elim _ _
    simp [lossOf, lossVec, correctArm, Expert.mk]

/-- Under `S_0`, the law of the two bits `(z, c)` gives mass `P(z) / 2` to `(z, c)`. -/
lemma map_lossRandomness_zero_singleton (z c : Bool) :
    (lossRandomness 1 ε).map (fun r ↦ (r.1, r.2.1 0)) {(z, c)} =
      bern (1 / 2 - ε / 2) {z} * 2⁻¹ := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have : (fun r : Bool × (Fin 1 → Bool) × Bool ↦ (r.1, r.2.1 0)) ⁻¹' {(z, c)} =
      {z} ×ˢ ({fun _ ↦ c} ×ˢ Set.univ) := by
    ext ⟨z', c', f'⟩
    simp [funext_iff, Fin.forall_fin_one]
  rw [this, lossRandomness, Measure.prod_prod, Measure.prod_prod,
    PMF.toMeasure_uniformOfFintype_singleton, measure_univ]
  simp

/-- Under `S_(1, v)`, with `b` the bit of the expert `(1, v)`, the law of the two bits `(z, c)`
gives mass `P(z) Ber(1/2 - ε)(b xor c)` to `(z, c)`. -/
lemma map_lossRandomness_mk_singleton (b z c : Bool) :
    (lossRandomness 1 ε).map (fun r ↦ (r.1, xor b r.2.2)) {(z, c)} =
      bern (1 / 2 - ε / 2) {z} * bern (1 / 2 - ε) {xor b c} := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have : (fun r : Bool × (Fin 1 → Bool) × Bool ↦ (r.1, xor b r.2.2)) ⁻¹' {(z, c)} =
      {z} ×ˢ (Set.univ ×ˢ {xor b c}) := by
    ext ⟨z', c', f'⟩
    cases b <;> cases c <;> cases f' <;> simp
  rw [this, lossRandomness, Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]

/-- The likelihood ratio of the correct bit `c` of batch `1` under `S_(1, v)` with respect to
`S_0`, given the bit `b` of the expert `(1, v)`: `1 + 2ε` if `c = b`, `1 - 2ε` otherwise. -/
noncomputable def bitRatio (ε : ℝ) (b c : Bool) : ℝ≥0∞ :=
  if c = b then ENNReal.ofReal (1 + 2 * ε) else ENNReal.ofReal (1 - 2 * ε)

/-- The law of the two bits `(z, c)` under `S_(1, v)` has density `bitRatio ε b c` with respect to
their law under `S_0`, where `b` is the bit of the expert `(1, v)`. -/
lemma map_lossRandomness_mk_eq (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b : Bool) :
    (lossRandomness 1 ε).map (fun r ↦ (r.1, xor b r.2.2)) =
      ((lossRandomness 1 ε).map (fun r ↦ (r.1, r.2.1 0))).withDensity
        (fun p ↦ bitRatio ε b p.2) := by
  refine Measure.ext_of_singleton fun ⟨z, c⟩ ↦ ?_
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    map_lossRandomness_zero_singleton, map_lossRandomness_mk_singleton]
  have key : bern (1 / 2 - ε) {xor b c} = bitRatio ε b c * 2⁻¹ := by
    rw [bitRatio]
    by_cases hcb : c = b
    · subst hcb
      rw [ite_eq_left rfl, Bool.xor_self, bern_singleton_false (by linarith) (by linarith),
        ofReal_mul_inv_two]
      congr 1
      ring
    · have : xor b c = true := by cases b <;> cases c <;> simp_all
      rw [ite_eq_right hcb, this, bern_singleton_true (by linarith) (by linarith),
        ofReal_mul_inv_two]
      congr 1
      ring
  rw [key]
  ring

/-- Under `S_0`, the expectation of a function of the correct bit is its average over the two
values of the bit. -/
lemma lintegral_map_lossRandomness_zero (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (h : Bool → ℝ≥0∞) :
    ∫⁻ p, h p.2 ∂((lossRandomness 1 ε).map (fun r ↦ (r.1, r.2.1 0))) =
      (h true + h false) * 2⁻¹ := by
  rw [lintegral_fintype]
  simp_rw [Fintype.sum_prod_type, map_lossRandomness_zero_singleton, Fintype.sum_bool,
    bern_singleton_true (by linarith : (0 : ℝ) ≤ 1 / 2 - ε / 2) (by linarith),
    bern_singleton_false (by linarith : (0 : ℝ) ≤ 1 / 2 - ε / 2) (by linarith)]
  have : ENNReal.ofReal (1 / 2 - ε / 2) + ENNReal.ofReal (1 - (1 / 2 - ε / 2)) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_one]
    congr 1
    ring
  calc _ = (ENNReal.ofReal (1 / 2 - ε / 2) + ENNReal.ofReal (1 - (1 / 2 - ε / 2))) *
        ((h true + h false) * 2⁻¹) := by ring
    _ = _ := by rw [this, one_mul]

/-- The loss law under `S_0`, as the image of the law of the two bits. -/
lemma lossLaw_zero_eq (e : Expert 1 n → Arm 1) :
    lossLaw ε Expert.zero e =
      ((lossRandomness 1 ε).map (fun r ↦ (r.1, r.2.1 0))).map (Function.uncurry lossVec) := by
  rw [Measure.map_map measurable_lossVec (by fun_prop), lossLaw]
  congr 1
  funext r
  exact lossOf_zero_eq e r

/-- The loss law under `S_(1, v)`, as the image of the law of the two bits. -/
lemma lossLaw_mk_eq (v : Fin n) (e : Expert 1 n → Arm 1) :
    lossLaw ε (Expert.mk 0 v) e = ((lossRandomness 1 ε).map
      (fun r ↦ (r.1, xor (bitsOf e 0 v) r.2.2))).map (Function.uncurry lossVec) := by
  rw [Measure.map_map measurable_lossVec (by fun_prop), lossLaw]
  congr 1
  funext r
  exact lossOf_mk_eq v e r

/-! ### The density of a round -/

/-- The density of `roundLaw ε (Expert.mk 0 v)` with respect to `roundLaw ε Expert.zero` in the
two-batch game, `f_v` in the paper: `1 + 2ε` if the arm advised by the expert `(1, v)` has loss
`0` (it is the correct arm of batch `1`), `1 - 2ε` otherwise. -/
noncomputable def roundDensity (ε : ℝ) (v : Fin n) (g : AdvLoss 1 n) : ℝ≥0∞ :=
  if g.2 (Arm.ofBatch 0 (bitsOf g.1 0 v)) = 0 then ENNReal.ofReal (1 + 2 * ε)
  else ENNReal.ofReal (1 - 2 * ε)

/-- `roundDensity ε v` is measurable. -/
@[fun_prop]
lemma measurable_roundDensity (ε : ℝ) (v : Fin n) : Measurable (roundDensity ε v) := by
  refine measurable_from_prod_countable_right fun e ↦ ?_
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply
    (Arm.ofBatch 0 (bitsOf e 0 v))) measurable_const) measurable_const measurable_const

/-- `roundDensity ε v` is finite. -/
lemma roundDensity_ne_top (v : Fin n) (g : AdvLoss 1 n) : roundDensity ε v g ≠ ∞ := by
  unfold roundDensity
  split_ifs <;> exact ENNReal.ofReal_ne_top

/-- On the loss vector `lossVec z c`, the density `roundDensity ε v` is the likelihood ratio
`bitRatio` of the correct bit `c` given the bit of the expert `(1, v)`. -/
lemma roundDensity_lossVec (v : Fin n) (e : Expert 1 n → Arm 1) (z c : Bool) :
    roundDensity ε v (e, lossVec z c) = bitRatio ε (bitsOf e 0 v) c := by
  simp only [roundDensity, bitRatio, Arm.ofBatch, lossVec]
  by_cases h : bitsOf e 0 v = c
  · simp [h]
  · simp [h, Ne.symm h]

variable (ε) in
/-- Given the advice, the loss law under `S_(1, v)` has density `roundDensity ε v` with respect to
the loss law under `S_0`. -/
lemma lossLaw_mk_eq_withDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v : Fin n)
    (e : Expert 1 n → Arm 1) :
    lossLaw ε (Expert.mk 0 v) e =
      (lossLaw ε Expert.zero e).withDensity (fun ℓ ↦ roundDensity ε v (e, ℓ)) := by
  rw [lossLaw_mk_eq, lossLaw_zero_eq, withDensity_map measurable_lossVec
    (f := fun ℓ ↦ roundDensity ε v (e, ℓ))
    ((measurable_roundDensity ε v).comp measurable_prodMk_left), map_lossRandomness_mk_eq hε0 hε1]
  congr 2
  funext p
  exact (roundDensity_lossVec v e p.1 p.2).symm

/-- The loss kernel of `S_(1, v)` has density `roundDensity ε v` with respect to the loss kernel of
`S_0`. -/
lemma lossKernel_mk_eq_withDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v : Fin n) :
    lossKernel ε (Expert.mk 0 v) =
      (lossKernel ε Expert.zero).withDensity (fun e ℓ ↦ roundDensity ε v (e, ℓ)) := by
  ext1 e
  rw [Kernel.withDensity_apply _ (f := fun e ℓ ↦ roundDensity ε v (e, ℓ))
    (measurable_roundDensity ε v)]
  exact lossLaw_mk_eq_withDensity ε hε0 hε1 v e

/-- **Density of a round** (two-batch game). For `0 ≤ ε ≤ 1/2`, the law `P_(1, v)` of a round
under `S_(1, v)` has density `roundDensity ε v` with respect to the law `P_0` under `S_0`. -/
lemma roundLaw_mk_eq_withDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v : Fin n) :
    roundLaw ε (Expert.mk 0 v) = (roundLaw ε Expert.zero).withDensity (roundDensity ε v) := by
  have : IsSFiniteKernel
      ((lossKernel ε Expert.zero).withDensity fun e ℓ ↦ roundDensity ε v (e, ℓ)) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ roundDensity_ne_top v _
  rw [roundLaw, roundLaw, lossKernel_mk_eq_withDensity hε0 hε1,
    Measure.compProd_withDensity (g := fun e ℓ ↦ roundDensity ε v (e, ℓ))
      (measurable_roundDensity ε v)]

/-- `roundDensity ε v` is a probability density with respect to `P_0`. -/
lemma lintegral_roundDensity_zero (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v : Fin n) :
    ∫⁻ g, roundDensity ε v g ∂(roundLaw ε Expert.zero) = 1 := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← roundLaw_mk_eq_withDensity hε0 hε1, measure_univ]

/-- **Products of rounds.** `P_(1, v)^T` has density `g ↦ ∏_t f_v(g_t)` with respect to `P_0^T`. -/
lemma pi_roundLaw_mk_eq_withDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v : Fin n) (T : ℕ) :
    (Measure.pi fun _ : Fin T ↦ roundLaw ε (Expert.mk 0 v)) =
      (Measure.pi fun _ : Fin T ↦ roundLaw ε Expert.zero).withDensity
        (fun x ↦ ∏ t, roundDensity ε v (x t)) := by
  have : SigmaFinite ((roundLaw ε Expert.zero).withDensity (roundDensity ε v)) := by
    rw [← roundLaw_mk_eq_withDensity hε0 hε1]
    infer_instance
  simp_rw [roundLaw_mk_eq_withDensity hε0 hε1 v]
  exact Measure.pi_withDensity fun _ ↦ measurable_roundDensity ε v

/-! ### Expected likelihood ratios -/

/-- `bitRatio ε b c + bitRatio ε (!b) c = (1 + 2ε) + (1 - 2ε) = 2`. -/
lemma bitRatio_add_bitRatio_not (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b c : Bool) :
    bitRatio ε b c + bitRatio ε (!b) c = 2 := by
  cases b <;> cases c <;> simp [bitRatio, ofReal_one_add_add_ofReal_one_sub hε0 hε1, add_comm]

/-- `bitRatio ε b true + bitRatio ε b false = (1 + 2ε) + (1 - 2ε) = 2`. -/
lemma bitRatio_true_add_bitRatio_false (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b : Bool) :
    bitRatio ε b true + bitRatio ε b false = 2 := by
  cases b <;> simp [bitRatio, ofReal_one_add_add_ofReal_one_sub hε0 hε1, add_comm]

/-- The expectation under `S_0` of the product of the likelihood ratios of two experts of batch `1`
with bits `b₁`, `b₂`, given these bits: the correct bit is uniform. -/
noncomputable def pairRatio (ε : ℝ) (b₁ b₂ : Bool) : ℝ≥0∞ :=
  (bitRatio ε b₁ true * bitRatio ε b₂ true + bitRatio ε b₁ false * bitRatio ε b₂ false) * 2⁻¹

/-- For a single expert, `pairRatio ε b b = ((1 + 2ε)² + (1 - 2ε)²) / 2 = 1 + 4ε²`. -/
lemma pairRatio_self (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b : Bool) :
    pairRatio ε b b = ENNReal.ofReal (1 + 4 * ε ^ 2) := by
  have h : (ENNReal.ofReal (1 + 2 * ε) * ENNReal.ofReal (1 + 2 * ε) +
      ENNReal.ofReal (1 - 2 * ε) * ENNReal.ofReal (1 - 2 * ε)) * 2⁻¹ =
      ENNReal.ofReal (1 + 4 * ε ^ 2) := by
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith), ofReal_mul_inv_two]
    congr 1
    ring
  cases b <;> simp only [pairRatio, bitRatio] <;> simp [add_comm, h]

/-- Flipping the first bit maps `pairRatio` to `2 - pairRatio`. -/
lemma pairRatio_add_pairRatio_not (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b₁ b₂ : Bool) :
    pairRatio ε b₁ b₂ + pairRatio ε (!b₁) b₂ = 2 := by
  have h1 := bitRatio_add_bitRatio_not hε0 hε1 b₁ true
  have h2 := bitRatio_add_bitRatio_not hε0 hε1 b₁ false
  have h3 := bitRatio_true_add_bitRatio_false hε0 hε1 b₂
  calc pairRatio ε b₁ b₂ + pairRatio ε (!b₁) b₂
      = ((bitRatio ε b₁ true + bitRatio ε (!b₁) true) * bitRatio ε b₂ true +
        (bitRatio ε b₁ false + bitRatio ε (!b₁) false) * bitRatio ε b₂ false) * 2⁻¹ := by
        simp only [pairRatio]; ring
    _ = 2 * (bitRatio ε b₂ true + bitRatio ε b₂ false) * 2⁻¹ := by rw [h1, h2]; ring
    _ = 2 := by
        rw [h3, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- Flip the bit of the expert `(u, v)` for every batch `u`. -/
def flipBit (v : Fin n) (b : Bits 1 n) : Bits 1 n :=
  fun u v' ↦ if v' = v then !b u v' else b u v'

/-- `flipBit v` is an involution. -/
lemma flipBit_involutive (v : Fin n) : Function.Involutive (flipBit v) := by
  intro b
  funext u v'
  by_cases h : v' = v <;> simp [flipBit, h]

/-- For two distinct experts `(1, v)`, `(1, w)`, the expectation of `pairRatio` over uniform
advice bits is `1`: flipping the bit of `(1, v)` maps `pairRatio` to `2 - pairRatio`. -/
lemma lintegral_pairRatio_of_ne (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {v w : Fin n} (hvw : v ≠ w) :
    ∫⁻ b, pairRatio ε (b 0 v) (b 0 w) ∂(uniformBits 1 n) = 1 := by
  set G : Bits 1 n → ℝ≥0∞ := fun b ↦ pairRatio ε (b 0 v) (b 0 w) with hG_def
  have hG b : G b + G ((flipBit_involutive v).toPerm _ b) = 2 := by
    simp only [hG_def, Function.Involutive.coe_toPerm, flipBit, ite_eq_right (Ne.symm hvw)]
    exact pairRatio_add_pairRatio_not hε0 hε1 (b 0 v) (b 0 w)
  have h_two : ∫⁻ b, G b ∂(uniformBits 1 n) + ∫⁻ b, G b ∂(uniformBits 1 n) = 2 := by
    rw [uniformBits]
    conv_lhs => arg 2; rw [← PMF.lintegral_uniformOfFintype_comp_equiv
      ((flipBit_involutive v).toPerm _) G]
    rw [← lintegral_add_left (measurable_of_countable _)]
    simp_rw [hG, lintegral_const, measure_univ, mul_one]
  rw [← two_mul] at h_two
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp (h_two.trans (mul_one 2).symm)

/-- The bits of the advice given by the bits `b` are `b`. -/
lemma bitsOf_adviceOf {k : ℕ} (b : Bits k n) : bitsOf (adviceOf b) = b := rfl

/-- The expectation under `P_0` of the product of the likelihood ratios of `(1, v)` and `(1, w)`
is `1 + 4ε²` if `v = w` and `1` otherwise. -/
lemma lintegral_roundDensity_mul (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v w : Fin n) :
    ∫⁻ g, roundDensity ε v g * roundDensity ε w g ∂(roundLaw ε Expert.zero) =
      if v = w then ENNReal.ofReal (1 + 4 * ε ^ 2) else 1 := by
  have h_inner (e : Expert 1 n → Arm 1) :
      ∫⁻ ℓ, roundDensity ε v (e, ℓ) * roundDensity ε w (e, ℓ) ∂(lossKernel ε Expert.zero e) =
        pairRatio ε (bitsOf e 0 v) (bitsOf e 0 w) := by
    change ∫⁻ ℓ, _ ∂(lossLaw ε Expert.zero e) = _
    rw [lossLaw_zero_eq, lintegral_map (by fun_prop) measurable_lossVec]
    simp_rw [Function.uncurry, roundDensity_lossVec]
    rw [lintegral_map_lossRandomness_zero hε0 hε1 (fun c ↦ bitRatio ε (bitsOf e 0 v) c *
      bitRatio ε (bitsOf e 0 w) c), pairRatio]
  rw [roundLaw, Measure.lintegral_compProd (by fun_prop)]
  simp_rw [h_inner]
  rw [initAdvice, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp_rw [bitsOf_adviceOf]
  split_ifs with hvw
  · subst hvw
    simp_rw [pairRatio_self hε0 hε1]
    rw [lintegral_const, measure_univ, mul_one]
  · exact lintegral_pairRatio_of_ne hε0 hε1 hvw

/-- **Expected likelihood ratio of a round.** The expectation under `P_(1, w)` of the likelihood
ratio `f_v` of `P_(1, v)` with respect to `P_0` is `1 + 4ε²` if `v = w` and `1` otherwise. -/
lemma lintegral_roundDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v w : Fin n) :
    ∫⁻ g, roundDensity ε v g ∂(roundLaw ε (Expert.mk 0 w)) =
      if v = w then ENNReal.ofReal (1 + 4 * ε ^ 2) else 1 := by
  rw [roundLaw_mk_eq_withDensity hε0 hε1,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ← lintegral_roundDensity_mul hε0 hε1 v w]
  congr with g
  exact mul_comm _ _

/-- **Expected likelihood ratios** (two-batch game). The expectation under `P_(1, w)^T` of the
likelihood ratio `g ↦ ∏_t f_v(g_t)` of `P_(1, v)^T` with respect to `P_0^T` is `(1 + 4ε²)^T` if
`v = w` and `1` otherwise. -/
lemma lintegral_prod_roundDensity (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (v w : Fin n) (T : ℕ) :
    ∫⁻ x, ∏ t, roundDensity ε v (x t) ∂(Measure.pi fun _ : Fin T ↦ roundLaw ε (Expert.mk 0 w)) =
      if v = w then ENNReal.ofReal ((1 + 4 * ε ^ 2) ^ T) else 1 := by
  rw [lintegral_fintype_prod_eq_pow (measurable_roundDensity ε v),
    lintegral_roundDensity hε0 hε1, Fintype.card_fin]
  split_ifs
  · rw [ENNReal.ofReal_pow (by positivity)]
  · exact one_pow T

end Chase2026Tight
