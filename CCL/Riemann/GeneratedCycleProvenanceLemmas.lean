import CCL.Riemann.GeneratedCycleProvenance

/-!
# Algebra of generated cycle-position traces

These lemmas stay downstream of the trace data type so adding derived
provenance facts does not invalidate the generated geometry dependency DAG.
-/

namespace CCL.Riemann.GeneratedCycleProvenance.PositionTrace

/-- Adjacent consecutive traces compose to the trace of their union. -/
theorem append_consecutive (start leftCount rightCount : Nat) :
    append (consecutive start leftCount)
        (consecutive (start + leftCount) rightCount) =
      consecutive start (leftCount + rightCount) := by
  cases leftCount with
  | zero => simp only [consecutive, Nat.add_zero, Nat.zero_add, empty_append]
  | succ left =>
      cases rightCount with
      | zero =>
          simp only [consecutive, append_empty]
      | succ right =>
          simp only [consecutive, append, boundaryBreak, Nat.add_eq, if_true,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every adjacent pair in a displayed list occupies successive row
positions.  This is the pointwise meaning encoded by a zero-break trace. -/
inductive Successive {alpha : Type} (position : alpha -> Nat) :
    List alpha -> Prop
  | nil : Successive position []
  | singleton (value : alpha) : Successive position [value]
  | cons (first second : alpha) (remaining : List alpha) :
      position first + 1 = position second ->
      Successive position (second :: remaining) ->
      Successive position (first :: second :: remaining)

theorem ofList_cons_endpoints {alpha : Type} (position : alpha -> Nat)
    (first : alpha) : forall remaining : List alpha,
    exists last,
      (ofList position (first :: remaining)).endpoints =
        .occupied (position first) last
  | [] => ⟨position first, by rfl⟩
  | second :: remaining => by
      rcases ofList_cons_endpoints position second remaining with
        ⟨last, tailEndpoints⟩
      refine ⟨last, ?_⟩
      change (append (singleton (position first))
        (ofList position (second :: remaining))).endpoints = _
      unfold append
      rw [tailEndpoints]
      rfl

/-- A trace with no recorded break yields the corresponding pointwise
successor relation on the original data list. -/
theorem successive_of_breaks_zero {alpha : Type} (position : alpha -> Nat) :
    forall values : List alpha,
      (ofList position values).breaks = 0 -> Successive position values
  | [], _ => .nil
  | [value], _ => .singleton value
  | first :: second :: remaining, noBreaks => by
      rcases ofList_cons_endpoints position second remaining with
        ⟨last, tailEndpoints⟩
      have sumZero :
          (ofList position (second :: remaining)).breaks +
              boundaryBreak (.occupied (position first) (position first))
                (.occupied (position second) last) = 0 := by
        have expanded :
            (append (singleton (position first))
              (ofList position (second :: remaining))).breaks = 0 := by
          exact noBreaks
        simp only [append, singleton, Nat.zero_add] at expanded
        rw [tailEndpoints] at expanded
        exact expanded
      have tailNoBreaks :
          (ofList position (second :: remaining)).breaks = 0 :=
        (Nat.eq_zero_of_add_eq_zero sumZero).1
      have boundaryZero :
          boundaryBreak (.occupied (position first) (position first))
            (.occupied (position second) last) = 0 :=
        (Nat.eq_zero_of_add_eq_zero sumZero).2
      have adjacent : position first + 1 = position second := by
        by_cases equal : position first + 1 = position second
        · exact equal
        · simp only [boundaryBreak, equal, if_false] at boundaryZero
          contradiction
      exact .cons first second remaining adjacent
        (successive_of_breaks_zero position (second :: remaining)
          tailNoBreaks)

/-- A pointwise-successive nonempty list maps to the canonical consecutive
natural-number range beginning at its first position. -/
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

/-- Exact list-level content of a compact coverage certificate.  This closes
the gap between the constant-size trace and its intended data-level meaning:
the mapped positions are the displayed canonical interval, hence contain no
omissions, repetitions, or reordering. -/
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
      exact (successive_of_breaks_zero position (first :: remaining)
        (by
          have breaksEq := congrArg PositionTrace.breaks coverage.exact
          simpa only [consecutive] using breaksEq)).map_eq_range'

end CCL.Riemann.GeneratedCycleProvenance.PositionTrace
