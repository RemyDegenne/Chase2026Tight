/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Hitting times of a union of sets

If a process does not visit `t` between the time `n` and its hitting time of `s` (included), then
it hits `s ∪ t` at the same time as `s`.

We also record that `WithTop.untopA t ≤ t`, so that the value of a process stopped at a time `t`
is the value at a time at most `t`.

## Main statements

* `MeasureTheory.hittingAfter_union_of_forall_notMem`: the hitting time of `s ∪ t` is the hitting
  time of `s` if the process does not visit `t` before.
* `WithTop.coe_untopA_le`: `(t.untopA : WithTop α) ≤ t`.
-/

@[expose] public section

namespace WithTop

/-- The finite value `untopA t` of `t : WithTop α` (an arbitrary element if `t = ⊤`) is at most
`t`. -/
lemma coe_untopA_le {α : Type*} [Preorder α] [Nonempty α] (t : WithTop α) :
    ((t.untopA : α) : WithTop α) ≤ t := by
  cases t with
  | top => exact le_top
  | coe m => exact le_of_eq (by simp [WithTop.untopA])

end WithTop

namespace MeasureTheory

variable {Ω β ι : Type*} [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  {u : ι → Ω → β} {s t : Set β} {n : ι} {ω : Ω}

/-- If the process `u` does not visit `t` from time `n` up to its hitting time of `s` (included),
then it hits `s ∪ t` at the same time as `s`. -/
lemma hittingAfter_union_of_forall_notMem
    (h : ∀ i, n ≤ i → (i : WithTop ι) ≤ hittingAfter u s n ω → u i ω ∉ t) :
    hittingAfter u (s ∪ t) n ω = hittingAfter u s n ω := by
  refine le_antisymm (hittingAfter_anti u n Set.subset_union_left ω) ?_
  cases hst : hittingAfter u (s ∪ t) n ω with
  | top => exact le_top
  | coe i =>
    have hni : n ≤ i := by
      have := le_hittingAfter (u := u) (s := s ∪ t) (n := n) ω
      rw [hst] at this
      exact_mod_cast this
    have hmem : u i ω ∈ s ∪ t := by
      have := hittingAfter_mem_set_of_ne_top (u := u) (s := s ∪ t) (n := n) (ω := ω)
        (by simp [hst])
      rwa [hst] at this
    refine not_lt.1 fun hlt ↦ ?_
    rcases hmem with hs | ht
    · exact notMem_of_lt_hittingAfter hlt hni hs
    · exact h i hni hlt.le ht

end MeasureTheory
