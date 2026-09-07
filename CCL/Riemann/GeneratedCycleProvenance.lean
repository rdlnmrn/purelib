import mathlib.Data.ConstructiveList

/-!
# Compact provenance for generated finite cycle meshes

Large generated cycle certificates should not force downstream clients to
recompute a list of thousands of row positions merely to see that every row
was retained in traversal order.  This module defines a constant-size summary
of such a finite list.  The summary is useful only together with its exact
equality to `ofList`; generated clients cache the former and retain the latter
as a proof field.
-/

namespace CCL.Riemann.GeneratedCycleProvenance

/-- The first and last row positions of a finite list, with emptiness made
impossible to confuse with a partially populated endpoint cache. -/
inductive PositionEndpoints
  | empty
  | occupied (first last : Nat)
  deriving DecidableEq, Repr

/-- Constant-size traversal summary.  `breaks` counts adjacent pairs which
are not exact successors. -/
structure PositionTrace where
  count : Nat
  endpoints : PositionEndpoints
  breaks : Nat
  deriving DecidableEq, Repr

namespace PositionTrace

def empty : PositionTrace :=
  { count := 0, endpoints := .empty, breaks := 0 }

def singleton (position : Nat) : PositionTrace :=
  { count := 1, endpoints := .occupied position position, breaks := 0 }

def boundaryBreak : PositionEndpoints -> PositionEndpoints -> Nat
  | .occupied _ leftLast, .occupied rightFirst _ =>
      if leftLast + 1 = rightFirst then 0 else 1
  | _, _ => 0

/-- Concatenate two cached traces, checking exactly their one new boundary. -/
def append (left right : PositionTrace) : PositionTrace :=
  { count := left.count + right.count
    endpoints :=
      match left.endpoints, right.endpoints with
      | .empty, rightEndpoints => rightEndpoints
      | leftEndpoints, .empty => leftEndpoints
      | .occupied first _, .occupied _ last => .occupied first last
    breaks := left.breaks + right.breaks +
      boundaryBreak left.endpoints right.endpoints }

@[simp] theorem empty_append (trace : PositionTrace) :
    append empty trace = trace := by
  cases trace with
  | mk count endpoints breaks =>
      cases endpoints <;>
        simp only [append, empty, boundaryBreak, Nat.zero_add, Nat.add_zero]

@[simp] theorem append_empty (trace : PositionTrace) :
    append trace empty = trace := by
  cases trace with
  | mk count endpoints breaks =>
      cases endpoints <;> simp only [append, empty, boundaryBreak,
        Nat.add_zero]

theorem append_assoc (first second third : PositionTrace) :
    append (append first second) third =
      append first (append second third) := by
  cases first with
  | mk firstCount firstEndpoints firstBreaks =>
      cases second with
      | mk secondCount secondEndpoints secondBreaks =>
          cases third with
          | mk thirdCount thirdEndpoints thirdBreaks =>
              cases firstEndpoints <;> cases secondEndpoints <;>
                cases thirdEndpoints <;>
                simp only [append, boundaryBreak, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]

/-- Exact trace computed from a displayed finite list. -/
def ofList {alpha : Type} (position : alpha -> Nat) :
    List alpha -> PositionTrace
  | [] => empty
  | value :: remaining =>
      append (singleton (position value)) (ofList position remaining)

@[simp] theorem ofList_count {alpha : Type} (position : alpha -> Nat) :
    forall values : List alpha,
      (ofList position values).count = values.length
  | [] => rfl
  | value :: remaining => by
      simp only [ofList, append, singleton, List.length_cons,
        ofList_count position remaining, Nat.add_comm]

theorem ofList_append {alpha : Type} (position : alpha -> Nat) :
    forall (first second : List alpha),
      ofList position (first ++ second) =
        append (ofList position first) (ofList position second)
  | [], second => by
      simp only [List.nil_append, ofList, empty_append]
  | value :: remaining, second => by
      simp only [List.cons_append, ofList]
      rw [ofList_append position remaining second]
      exact (append_assoc (singleton (position value))
        (ofList position remaining) (ofList position second)).symm

/-- Expected trace of `count` consecutive positions beginning at `start`. -/
def consecutive (start : Nat) : Nat -> PositionTrace
  | 0 => empty
  | count + 1 =>
      { count := count + 1
        endpoints := .occupied start (start + count)
        breaks := 0 }

@[simp] theorem consecutive_count (start count : Nat) :
    (consecutive start count).count = count := by
  cases count <;> rfl

/-- Inspectable evidence that an actual finite list occupies every successive
row position in one displayed interval.  The equality targets `ofList`, so a
cached trace cannot be substituted for the data it is meant to certify. -/
structure Coverage {alpha : Type} (position : alpha -> Nat)
    (values : List alpha) (start count : Nat) : Prop where
  exact : ofList position values = consecutive start count

theorem Coverage.length {alpha : Type} {position : alpha -> Nat}
    {values : List alpha} {start count : Nat}
    (coverage : Coverage position values start count) :
    values.length = count := by
  calc
    values.length = (ofList position values).count :=
      (ofList_count position values).symm
    _ = (consecutive start count).count :=
      congrArg PositionTrace.count coverage.exact
    _ = count := consecutive_count start count

end PositionTrace

end CCL.Riemann.GeneratedCycleProvenance
