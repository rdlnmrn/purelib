module

meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity
import Mathlib.Tactic.Linter.Lint

/-!
# Finite position traces

A position trace retains the entry count, first and last endpoints and the
number of adjacency failures in a finite list. Append combines these summaries
in their original order. Coverage certifies equality with the summary of a
consecutive natural interval, retaining the original position function and list.
-/

public section

namespace Purelib.Data.List

namespace PositionTrace.Basic

set_option genInjectivity false in

/-- Retain either an empty position summary or its first and last positions.

The nonempty case stores natural endpoints directly; validity as endpoints of an
actual list is supplied by the surrounding trace equality. -/
inductive PositionEndpoints
  /-- There are no endpoints in the empty summary. -/ | empty
  /-- Retain the first and last natural positions of a nonempty summary. -/ | occupied (first last : Nat)
  deriving @[expose] DecidableEq

constructive_injectivity PositionEndpoints

derive_exposed_repr PositionEndpoints

end PositionTrace.Basic

open PositionTrace.Basic

set_option genInjectivity false in
/-- Summarize the count, endpoints and adjacency failures of finite positions.

The summary composes by append. An adjacency failure occurs when successive positions
are not consecutive; arbitrary records acquire list meaning through the retained
ofList equality. -/
structure PositionTrace where
  /-- The number of summarized entries. -/ count : Nat
  /-- The retained first and last positions, or the empty endpoint marker. -/ endpoints : PositionEndpoints
  /-- The number of adjacent position pairs that fail the successor test. -/ breaks : Nat
  deriving @[expose] DecidableEq

constructive_injectivity PositionTrace

derive_exposed_repr PositionTrace

namespace PositionTrace

/-- The position trace with no entries, no endpoints and no adjacency failures. -/
@[expose] def empty : PositionTrace :=
  { count := 0, endpoints := .empty, breaks := 0 }

/-- The position trace of one retained natural position. -/
@[expose] def singleton (position : Nat) : PositionTrace :=
  { count := 1, endpoints := .occupied position position, breaks := 0 }

set_option backward.match.sparseCases false in
/-- Count the single possible adjacency failure between two position traces.

Return one precisely when both traces are nonempty and the right first position is
not the successor of the left last position; otherwise return zero. -/
@[expose] def boundaryBreak : PositionEndpoints -> PositionEndpoints -> Nat
  | .occupied _ leftLast, .occupied rightFirst _ =>
      if leftLast + 1 = rightFirst then 0 else 1
  | _, _ => 0

/-- Combine two position summaries in their displayed order.

Counts and internal failures add; the boundary contributes its exact zero-or-one
failure. Empty sides contribute no endpoint, while nonempty sides retain the outer
endpoints. -/
@[expose] def append (left right : PositionTrace) : PositionTrace :=
  { count := left.count + right.count
    endpoints :=
      match left.endpoints, right.endpoints with
      | .empty, rightEndpoints => rightEndpoints
      | leftEndpoints, .empty => leftEndpoints
      | .occupied first _, .occupied _ last => .occupied first last
    breaks := left.breaks + right.breaks +
      PositionTrace.boundaryBreak left.endpoints right.endpoints }

/-- The empty position trace is a left identity for trace append. -/
@[simp] theorem empty_append (trace : PositionTrace) :
    PositionTrace.append PositionTrace.empty trace = trace := by
  cases trace with
  | mk count endpoints breaks =>
      cases endpoints <;>
        simp only [PositionTrace.append, PositionTrace.empty, PositionTrace.boundaryBreak, Nat.zero_add, Nat.add_zero,
          -eq_self, -iff_self] <;> rfl

/-- The empty position trace is a right identity for trace append. -/
@[simp] theorem append_empty (trace : PositionTrace) :
    PositionTrace.append trace PositionTrace.empty = trace := by
  cases trace with
  | mk count endpoints breaks =>
      cases endpoints <;> simp only [PositionTrace.append, PositionTrace.empty, PositionTrace.boundaryBreak,
        Nat.add_zero, -eq_self, -iff_self] <;> rfl

/-- Position-trace append is associative, including the boundary-failure count.

The statement applies to arbitrary retained summaries. Endpoint cases identify the
same boundary comparisons on both parenthesizations. -/
theorem append_assoc (first second third : PositionTrace) :
    PositionTrace.append (PositionTrace.append first second) third =
      PositionTrace.append first (PositionTrace.append second third) := by
  cases first with
  | mk firstCount firstEndpoints firstBreaks =>
      cases second with
      | mk secondCount secondEndpoints secondBreaks =>
          cases third with
          | mk thirdCount thirdEndpoints thirdBreaks =>
              cases firstEndpoints <;> cases secondEndpoints <;>
                cases thirdEndpoints <;>
                simp only [PositionTrace.append, PositionTrace.boundaryBreak, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm, -eq_self, -iff_self] <;> rfl

/-- Summarize a finite list by reading each entry's retained natural position.

Append the singleton head summary to the recursively summarized tail, retaining exact
count, outer endpoints and every adjacent discontinuity. -/
@[expose] def ofList {alpha : Type} (position : alpha -> Nat) :
    List alpha -> PositionTrace
  | [] => PositionTrace.empty
  | value :: remaining =>
      PositionTrace.append (PositionTrace.singleton (position value)) (PositionTrace.ofList position remaining)

/-- The count in a finite list's position trace equals its length. -/
@[simp] theorem ofList_count {alpha : Type} (position : alpha -> Nat) :
    forall values : List alpha,
      (PositionTrace.ofList position values).count = values.length
  | [] => rfl
  | value :: remaining => by
      simp only [PositionTrace.ofList, PositionTrace.append, PositionTrace.singleton, List.length_cons,
        PositionTrace.ofList_count position remaining, Nat.add_comm, -eq_self, -iff_self]
      rfl

/-- Summarizing list concatenation equals appending the two position traces. -/
theorem ofList_append {alpha : Type} (position : alpha -> Nat) :
    forall (first second : List alpha),
      PositionTrace.ofList position (first ++ second) =
        PositionTrace.append (PositionTrace.ofList position first) (PositionTrace.ofList position second)
  | [], second => by
      simp only [List.nil_append, PositionTrace.ofList, PositionTrace.empty_append, -eq_self, -iff_self]
      rfl
  | value :: remaining, second => by
      simp only [List.cons_append, PositionTrace.ofList, -eq_self, -iff_self]
      rw [PositionTrace.ofList_append position remaining second]
      exact (PositionTrace.append_assoc (PositionTrace.singleton (position value))
        (PositionTrace.ofList position remaining) (PositionTrace.ofList position second)).symm

/-- Build the position summary of a consecutive interval of the given length.

Zero length gives the empty summary. A positive length retains the starting position
and the last position start + count - 1, with no adjacency failures. -/
@[expose] def consecutive (start : Nat) : Nat -> PositionTrace
  | 0 => PositionTrace.empty
  | count + 1 =>
      { count := count + 1
        endpoints := .occupied start (start + count)
        breaks := 0 }

/-- A consecutive interval summary retains exactly its supplied count. -/
@[simp] theorem consecutive_count (start count : Nat) :
    (PositionTrace.consecutive start count).count = count := by
  cases count <;> rfl

/-- Certify that a displayed list has exactly the trace of a supplied consecutive
interval.

The equality retains the position function, original list, start and count. It fixes
the endpoints and excludes every adjacency break, including the empty case. -/
structure Coverage {alpha : Type} (position : alpha -> Nat)
    (values : List alpha) (start count : Nat) : Prop where
  /-- The original list's position trace equals the requested consecutive interval summary. -/ exact :
    PositionTrace.ofList position values = PositionTrace.consecutive start count

namespace Coverage

/-- Exact interval coverage fixes the original list length to the requested count. -/
theorem length {alpha : Type} {position : alpha -> Nat}
    {values : List alpha} {start count : Nat}
    (coverage : Coverage position values start count) :
    values.length = count := by
  calc
    values.length = (PositionTrace.ofList position values).count :=
      (PositionTrace.ofList_count position values).symm
    _ = (PositionTrace.consecutive start count).count :=
      congrArg PositionTrace.count coverage.exact
    _ = count := PositionTrace.consecutive_count start count

end Coverage
end PositionTrace

end Purelib.Data.List

end
