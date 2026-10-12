module

import Mathlib.Tactic.TypeStar

/-!
# Nonempty list maps

Mapping a function preserves a finite list's nonemptiness.
-/

namespace Purelib.Data.List.Map.Nonempty

/-- Mapping any function over a nonempty finite list produces a nonempty list. -/
public theorem map_ne_nil
    {A B : Type*} (function : A → B) {values : List A}
    (nonempty : values ≠ []) : values.map function ≠ [] := by
  cases values with
  | nil => exact (nonempty rfl).elim
  | cons value values => exact List.cons_ne_nil _ _

end Purelib.Data.List.Map.Nonempty
