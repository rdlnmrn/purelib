module

public import Purelib.Data.List.PositionTrace.Basic

open Purelib.Data.List.PositionTrace

/-!
# Algebra of finite position traces

Trace append respects consecutive intervals. Exact coverage fixes the original
position list to its requested natural range, including empty intervals.
-/

public section

namespace Purelib.Data.List.PositionTrace.Laws

open Purelib.Data.List.PositionTrace.Basic
open Purelib.Data.List.PositionTrace

/-- Appending adjacent consecutive interval summaries yields their combined interval.

The second interval starts exactly after the first count. The result includes empty
intervals and retains zero internal and boundary failures. -/
theorem append_consecutive (start leftCount rightCount : Nat) :
    PositionTrace.append (PositionTrace.consecutive start leftCount)
        (PositionTrace.consecutive (start + leftCount) rightCount) =
      PositionTrace.consecutive start (leftCount + rightCount) := by
  cases leftCount with
  | zero =>
    simp only [PositionTrace.consecutive, Nat.add_zero, Nat.zero_add, PositionTrace.empty_append, -eq_self, -iff_self];
      rfl
  | succ left =>
      cases rightCount with
      | zero =>
          simp only [PositionTrace.consecutive, PositionTrace.append_empty, -eq_self, -iff_self]
          rfl
      | succ right =>
          simp only [PositionTrace.consecutive, PositionTrace.append, PositionTrace.boundaryBreak, Nat.add_eq,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, -eq_self, -iff_self]
          split
          · rfl
          · rename_i impossible
            exact (impossible rfl).elim

/-- Certify that every adjacent pair in a displayed list has consecutive positions.

Empty and singleton lists require no adjacency evidence. Each longer constructor
retains the next-position equality and the certificate on the original tail. -/
inductive Successive {alpha : Type} (position : alpha -> Nat) :
    List alpha -> Prop
  /-- The empty list has no adjacent-position obligations. -/ | nil : Successive position []
  /-- A singleton has no adjacent-position obligations. -/ | singleton (value : alpha) : Successive position [value]
  /-- Retain the successor relation of the first pair and successive positions throughout the original tail. -/ | cons
    (first second : alpha) (remaining : List alpha) :
      position first + 1 = position second ->
      Successive position (second :: remaining) ->
      Successive position (first :: second :: remaining)

/-- A nonempty list trace retains its head position as the first endpoint and some last
position. -/
theorem ofList_cons_endpoints {alpha : Type} (position : alpha -> Nat)
    (first : alpha) : forall remaining : List alpha,
    exists last,
      (PositionTrace.ofList position (first :: remaining)).endpoints =
        .occupied (position first) last
  | [] => ⟨position first, by rfl⟩
  | second :: remaining => by
      rcases ofList_cons_endpoints position second remaining with
        ⟨last, tailEndpoints⟩
      refine ⟨last, ?_⟩
      change (PositionTrace.append (singleton (position first))
        (PositionTrace.ofList position (second :: remaining))).endpoints = _
      unfold PositionTrace.append
      rw [tailEndpoints]
      rfl

/-- A list trace with no adjacency failures has consecutive positions at every adjacent
pair.

The trace's natural failure sum forces both the first boundary test and the retained
tail count to be zero; structural induction recovers every local equality. -/
theorem successive_of_breaks_zero {alpha : Type} (position : alpha -> Nat) :
    forall values : List alpha,
      (PositionTrace.ofList position values).breaks = 0 -> Successive position values
  | [], _ => .nil
  | [value], _ => .singleton value
  | first :: second :: remaining, noBreaks => by
      rcases ofList_cons_endpoints position second remaining with
        ⟨last, tailEndpoints⟩
      have sumZero :
          (PositionTrace.ofList position (second :: remaining)).breaks +
              PositionTrace.boundaryBreak (.occupied (position first) (position first))
                (.occupied (position second) last) = 0 := by
        have expanded :
            (PositionTrace.append (singleton (position first))
              (PositionTrace.ofList position (second :: remaining))).breaks = 0 := by
          exact noBreaks
        simp only [PositionTrace.append, PositionTrace.singleton, Nat.zero_add] at expanded
        rw [tailEndpoints] at expanded
        exact expanded
      have tailNoBreaks :
          (PositionTrace.ofList position (second :: remaining)).breaks = 0 :=
        (Nat.eq_zero_of_add_eq_zero sumZero).1
      have boundaryZero :
          PositionTrace.boundaryBreak (.occupied (position first) (position first))
            (.occupied (position second) last) = 0 :=
        (Nat.eq_zero_of_add_eq_zero sumZero).2
      have adjacent : position first + 1 = position second := by
        by_cases equal : position first + 1 = position second
        · exact equal
        · change (if position first + 1 = position second then 0 else 1) = 0 at boundaryZero
          rewrite [if_neg equal] at boundaryZero
          exact Nat.noConfusion boundaryZero
      exact .cons first second remaining adjacent
        (successive_of_breaks_zero position (second :: remaining)
          tailNoBreaks)

/-- A nonempty successive list maps to the consecutive natural range starting at its head
position. -/
theorem Successive.map_eq_range' {alpha : Type} {position : alpha -> Nat}
    {first : alpha} {remaining : List alpha}
    (successive : Successive position (first :: remaining)) :
    (first :: remaining).map position =
      List.range' (position first) (first :: remaining).length := by
  have all : forall {values : List alpha}, Successive position values ->
      match values with
      | [] => True
      | head :: tail =>
          values.map position =
            List.range' (position head) values.length := by
    intro values ordered
    induction ordered with
    | nil => exact True.intro
    | singleton value => rfl
    | cons firstValue secondValue remainingValues adjacent tail tailRange =>
        change position firstValue ::
            List.map position (secondValue :: remainingValues) =
          position firstValue :: List.range' (position firstValue + 1)
            (secondValue :: remainingValues).length
        rw [tailRange, adjacent]
  exact all successive

/-- Exact interval coverage identifies the mapped position list with the requested
natural range.

The retained trace equality fixes the length and first endpoint; zero breaks provide
all successive equalities, including the empty interval case. -/
theorem Coverage.positions_eq_range' {alpha : Type}
    {position : alpha -> Nat} {values : List alpha} {start count : Nat}
    (coverage : Coverage position values start count) :
    values.map position = List.range' start count := by
  cases values with
  | nil =>
      have countZero : count = 0 := by
        simpa only [List.length_nil] using coverage.length.symm
      subst count
      rfl
  | cons first remaining =>
      have countEq : count = remaining.length + 1 := by
        simpa only [List.length_cons, Nat.add_comm] using coverage.length.symm
      subst count
      have endpointsEq := congrArg PositionTrace.endpoints coverage.exact
      rcases ofList_cons_endpoints position first remaining with
        ⟨last, sourceEndpoints⟩
      rw [sourceEndpoints] at endpointsEq
      change PositionEndpoints.occupied (position first) last =
        PositionEndpoints.occupied start (start + remaining.length)
          at endpointsEq
      have firstEq : position first = start := by
        injection endpointsEq
      rw [← firstEq]
      exact (Laws.successive_of_breaks_zero position (first :: remaining)
        (by
          have breaksEq := congrArg PositionTrace.breaks coverage.exact
          simpa only [PositionTrace.consecutive] using breaksEq)).map_eq_range'

end Purelib.Data.List.PositionTrace.Laws

end
