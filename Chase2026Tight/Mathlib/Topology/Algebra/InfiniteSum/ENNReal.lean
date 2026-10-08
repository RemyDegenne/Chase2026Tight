/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Counting the natural numbers below an extended natural number

For `t : ℕ∞`, the number of natural numbers `i` with `i < t` is `t`, as an extended nonnegative
real: `∑' i : ℕ, 1{i < t} = t`.

## Main statements

* `ENNReal.tsum_ite_natCast_lt`: `∑' i : ℕ, (if (i : ℕ∞) < t then 1 else 0) = t`.
-/

@[expose] public section

open scoped ENNReal ENat

namespace ENNReal

/-- The number of natural numbers below `t : ℕ∞` is `t`. -/
lemma tsum_ite_natCast_lt (t : ℕ∞) : ∑' i : ℕ, (if (i : ℕ∞) < t then 1 else 0 : ℝ≥0∞) = t := by
  cases t with
  | top =>
    simp only [ENat.natCast_lt_top, ite_true, ENat.toENNReal_top]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  | coe m =>
    rw [tsum_eq_sum (s := Finset.range m)]
    · simp only [Nat.cast_lt, ENat.toENNReal_coe]
      rw [Finset.sum_ite_of_true (fun i hi ↦ Finset.mem_range.1 hi)]
      simp
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [Nat.cast_lt, not_lt.2 hi]

end ENNReal
