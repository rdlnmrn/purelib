module

import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Append

/-!
# Ordered finite natural ranges

The original range accumulator retains every natural index below its bound in
ascending order. Direct structural certificates describe its final appended
entry, membership bounds and front decomposition by successor mapping.
-/

namespace Purelib.Data.List.Range.Basic

open Purelib.Data.List

/-- Appending retained tail data commutes with the original natural range accumulator.

Induction on the original bound retains the same decreasing accumulator
steps. Each original natural index is prepended before the unchanged
appended tail, preserving the range's executable order. -/
private theorem range_loop_append : ∀ (bound : Nat) (before after : List Nat),
    List.range.loop bound (before ++ after) = List.range.loop bound before ++ after
  | 0, _, _ => rfl
  | bound + 1, before, after =>
      range_loop_append bound (bound :: before) after

/-- Incrementing the range bound appends that original bound as its last value.

The original accumulator construction retains the same displayed indices
in ascending order. Its appended tail law identifies the final singleton
without replacing the range algorithm. -/
public theorem range_succ (bound : Nat) :
    List.range (bound + 1) = List.range bound ++ [bound] :=
  range_loop_append bound [] [bound]

/-- The original finite natural range contains exactly its bound many entries.

Each successor range retains its earlier indices and appends the previous
bound as one final entry. Counting that same appended spine preserves the
original accumulator construction and its order. -/
public theorem length_range : ∀ bound : Nat, (List.range bound).length = bound
  | 0 => rfl
  | bound + 1 => by
      rewrite [range_succ, Append.length_append, length_range bound]
      exact Eq.refl _

/-- Membership in the finite natural range below a bound is equivalent to the strict bound.

The original successor range appends its previous bound. Membership in that
same ordered list is either in the earlier range or at its final singleton;
induction supplies the strict bound in both logical directions. -/
public theorem mem_range {value bound : Nat} :
    value ∈ List.range bound ↔ value < bound := by
  induction bound with
  | zero =>
      constructor
      · intro impossible
        nomatch impossible
      · intro impossible
        exact False.elim (Nat.not_lt_zero value impossible)
  | succ bound inductionHypothesis =>
      rw [range_succ]
      constructor
      · intro member
        rcases Membership.mem_append.mp member with earlier | last
        · exact Nat.lt_trans (inductionHypothesis.mp earlier)
            (Nat.lt_succ_self bound)
        · have equal : value = bound := Membership.mem_singleton.mp last
          exact equal.symm ▸ Nat.lt_succ_self bound
      · intro less
        have lessEqual : value ≤ bound := Nat.le_of_lt_succ less
        rcases Nat.lt_or_eq_of_le lessEqual with earlier | equal
        · exact Membership.mem_append.mpr
            (Or.inl (inductionHypothesis.mpr earlier))
        · exact Membership.mem_append.mpr
            (Or.inr (Membership.mem_singleton.mpr equal))

/-- A successor natural range starts at zero and continues with the successor map of the
previous range.

The original range retains its ascending natural indices. Increasing the bound
prepends zero and shifts each displayed previous entry by one, preserving their
order and their original accumulator construction. -/
public theorem range_succ_eq_map : ∀ count : Nat,
    List.range (count + 1) = 0 :: (List.range count).map Nat.succ
  | 0 => rfl
  | count + 1 => by
      calc
        List.range (count + 1 + 1) = List.range (count + 1) ++ [count + 1] :=
          range_succ (count + 1)
        _ = (0 :: (List.range count).map Nat.succ) ++ [count + 1] :=
          congrArg (fun values => values ++ [count + 1]) (range_succ_eq_map count)
        _ = 0 :: (List.range count ++ [count]).map Nat.succ := by rw [Map.map_append]; rfl
        _ = 0 :: (List.range (count + 1)).map Nat.succ := by rw [range_succ]

/-- Increasing a unit-step range appends its original final natural coordinate.

The retained starting coordinate and original range recursion preserve the
ordered prefix. The additional endpoint is the start plus the previous count. -/
public theorem range'_succ (start count : Nat) :
    List.range' start (count + 1) = List.range' start count ++ [start + count] := by
  induction count generalizing start with
  | zero => rfl
  | succ count retained =>
      change start :: List.range' (start + 1) (count + 1) =
        start :: (List.range' (start + 1) count ++ [start + (count + 1)])
      rewrite [retained]
      exact congrArg (fun last => start :: (List.range' (start + 1) count ++ [last]))
        ((Nat.succ_add start count).trans (Nat.add_succ start count).symm)

/-- Concatenating adjacent unit-step ranges gives their original combined range.

The first retained count determines the second range's starting coordinate. Each original natural entry keeps its order
and value. -/
public theorem range'_append_1 {start firstCount secondCount : Nat} :
    List.range' start firstCount ++ List.range' (start + firstCount) secondCount =
      List.range' start (firstCount + secondCount) := by
  induction firstCount generalizing start with
  | zero =>
      rewrite [Nat.zero_add]
      exact congrArg (fun initial => List.range' initial secondCount) (Nat.add_zero start)
  | succ firstCount ih =>
      rewrite [Nat.succ_add]
      change start :: (List.range' (start + 1) firstCount ++
        List.range' (start + (firstCount + 1)) secondCount) =
          start :: List.range' (start + 1) (firstCount + secondCount)
      have next : start + (firstCount + 1) = (start + 1) + firstCount :=
        (Nat.add_succ start firstCount).trans (Nat.succ_add start firstCount).symm
      rewrite [next, ih]
      exact Eq.refl _

end Purelib.Data.List.Range.Basic
