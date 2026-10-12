module

import Init.Data.List.Basic

namespace Purelib.Data.List.Replicate

/-- Replicating a supplied value retains exactly the requested number of entries.

Each successor request retains one copy before the original smaller replicated
list. Structural recursion counts those exact retained entries. -/
public theorem length_replicate {Alpha : Type u} (count : Nat) (value : Alpha) :
    (List.replicate count value).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ]
      exact congrArg Nat.succ ih

/-- Mapping a replicated value replicates its mapped value the same number of times.

Each retained copy produces one mapped entry. Structural recursion preserves
that original count and the unchanged replicated tail. -/
public theorem map_replicate {Alpha : Type u} {Beta : Type v}
    (function : Alpha → Beta) (count : Nat) (value : Alpha) :
    (List.replicate count value).map function =
      List.replicate count (function value) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.replicate_succ, List.map_cons]
      exact congrArg (List.cons (function value)) ih

/-- Replication of a sum concatenates the two original repeated blocks.

Each successor in the original left count retains one displayed entry before
its unchanged repeated tail. The original right block keeps its retained order. -/
public theorem replicate_add {Alpha : Type u} (left right : Nat) (value : Alpha) :
    List.replicate (left + right) value =
      List.replicate left value ++ List.replicate right value := by
  induction left with
  | zero => exact congrArg (fun count => List.replicate count value) (Nat.zero_add right)
  | succ left ih =>
      rewrite [Nat.succ_add, List.replicate_succ, ih, List.replicate_succ]
      exact Eq.refl _

end Purelib.Data.List.Replicate
