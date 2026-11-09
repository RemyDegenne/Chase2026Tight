/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.WithBot

/-!
# The finite value of an element of `WithTop α`

## Main statements

* `WithTop.coe_untopA_le`: `(t.untopA : WithTop α) ≤ t`; for instance the value of a process
  stopped at a time `t` is its value at a time at most `t`.
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
