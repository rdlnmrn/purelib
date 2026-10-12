module

public import Init.Data.List.Basic
import Purelib.Data.Nat.Division
import Purelib.Tactic.QuotientFreeOmega

/-!
# Stable finite merge sorting

Sorting retains Lean's original runtime algorithm: alternating forward and
reversed contiguous splits, tail-recursive merging and the supplied Boolean
comparison. Only the length indices and decreasing-call certificates use the
direct scalar proofs. Duplicate entries are retained; equal keys retain their
original order when the comparator chooses its left argument on equal keys.
-/

namespace Purelib.Data.List.Sort

universe u
variable {Alpha : Type u}

open Purelib.Data.Nat

set_option backward.match.sparseCases false

/-- Merge two retained lists by their original comparison and reversed accumulator.

The chosen original head is prepended to the accumulator at each step. An empty
input returns the same original reverseAux reading of that accumulator and the
unchanged other input, preserving the original tail-recursive runtime merge. -/
private def merge (left right : List Alpha) (compare : Alpha → Alpha → Bool) : List Alpha :=
  loop left right []
where
  /-- Consume one selected original merge head into the retained accumulator.

  The two original spines decrease in total length; an empty spine returns the
  same remaining original input after the accumulated prefix. -/
  loop : List Alpha → List Alpha → List Alpha → List Alpha
    | [], right, accumulated => List.reverseAux accumulated right
    | left, [], accumulated => List.reverseAux accumulated left
    | head :: tail, other :: remaining, accumulated =>
        if compare head other then
          loop tail (other :: remaining) (head :: accumulated)
        else loop (head :: tail) remaining (other :: accumulated)
  termination_by left right _ => left.length + right.length
  decreasing_by
    all_goals
      simp only [List.length_cons]
      omega0

/-- Split the original contiguous prefix into a reversed retained first part.

Exactly the supplied count of original heads is transferred to the accumulator,
leaving the unchanged suffix. The operation is the original splitRevAt algorithm. -/
private def splitRevAt (count : Nat) (values : List Alpha) : List Alpha × List Alpha :=
  loop values count []
where
  /-- Transfer the next retained original head until the split count is exhausted.

  The accumulator is returned directly with the original remaining tail; no
  second reversal or replacement list traversal is introduced. -/
  loop : List Alpha → Nat → List Alpha → List Alpha × List Alpha
    | head :: remaining, count + 1, accumulated =>
        loop remaining count (head :: accumulated)
    | remaining, _, accumulated => (accumulated, remaining)

/-- A bounded split consumes its original count and preserves the suffix length.

The same accumulator and original list spine are retained at each recursive
step. Constructor lengths transport both exact readings without changing data. -/
private theorem splitRevAt_loop_lengths :
    ∀ (values : List Alpha) (count : Nat) (accumulated : List Alpha),
      count ≤ values.length →
      (splitRevAt.loop values count accumulated).1.length = count + accumulated.length ∧
      (splitRevAt.loop values count accumulated).2.length = values.length - count
  | [], 0, accumulated, _ => by
      constructor
      · exact (Nat.zero_add accumulated.length).symm
      · rfl
  | [], count + 1, _, impossible => False.elim (Nat.not_succ_le_zero count impossible)
  | _ :: _, 0, accumulated, _ => by
      constructor
      · exact (Nat.zero_add accumulated.length).symm
      · rfl
  | head :: remaining, count + 1, accumulated, bounded => by
      have retained := splitRevAt_loop_lengths remaining count (head :: accumulated)
        (Nat.le_of_succ_le_succ bounded)
      constructor
      · change (splitRevAt.loop remaining count (head :: accumulated)).1.length =
          count + 1 + accumulated.length
        rewrite [retained.1]
        change count + (accumulated.length + 1) = count + 1 + accumulated.length
        omega0
      · change (splitRevAt.loop remaining count (head :: accumulated)).2.length =
          (remaining.length + 1) - (count + 1)
        rw [Nat.succ_sub_succ]
        exact retained.2

/-- The original bounded reversed split retains both exact component lengths.

Its empty initial accumulator contributes no entries. The supplied count
therefore identifies the original contiguous prefix and its remaining suffix. -/
private theorem splitRevAt_lengths (values : List Alpha) (count : Nat)
    (bounded : count ≤ values.length) :
    (splitRevAt count values).1.length = count ∧
      (splitRevAt count values).2.length = values.length - count := by
  have retained := splitRevAt_loop_lengths values count [] bounded
  exact ⟨retained.1.trans (Nat.add_zero count), retained.2⟩

/-- The two original halving coordinates reconstruct a retained natural length.

The original quotient and remainder equations and the two remainders below two
identify the complementary split counts, including the empty input. -/
private theorem half_lengths (count : Nat) :
    (count + 1) / 2 ≤ count ∧
      count - (count + 1) / 2 = count / 2 ∧
      count - count / 2 = (count + 1) / 2 := by
  have first := Division.mod_add_div (count + 1) 2
  have second := Division.mod_add_div count 2
  have firstSmall := Nat.mod_lt (count + 1) (Nat.zero_lt_succ 1)
  have secondSmall := Nat.mod_lt count (Nat.zero_lt_succ 1)
  constructor
  · omega0
  constructor <;> omega0

/-- Both retained halves are shorter than an original input with at least two entries.

The original quotient/remainder equations bound each split count. Those exact
indices certify recursive calls of the same alternating runtime algorithm. -/
private theorem halves_lt (offset : Nat) :
    (offset + 3) / 2 < offset + 2 ∧ (offset + 2) / 2 < offset + 2 := by
  have first := Division.mod_add_div (offset + 3) 2
  have second := Division.mod_add_div (offset + 2) 2
  constructor <;> omega0

/-- Split the original forward table with its longer half first and reversed.

Both returned tables retain the original splitRevAt data and exact length
indices; only their correctness proofs use the direct scalar certificates. -/
private def splitForward {count : Nat} (values : { values : List Alpha // values.length = count }) :
    { values : List Alpha // values.length = (count + 1) / 2 } ×
      { values : List Alpha // values.length = count / 2 } :=
  let result := splitRevAt ((count + 1) / 2) values.val
  have bounded : (count + 1) / 2 ≤ values.val.length := by
    rewrite [values.property]
    exact (half_lengths count).1
  have lengths := splitRevAt_lengths values.val ((count + 1) / 2) bounded
  (⟨result.1, lengths.1⟩, ⟨result.2, by
    apply lengths.2.trans
    rewrite [values.property]
    exact (half_lengths count).2.1⟩)

/-- Split the original reversed table with its shorter half first and reversed.

Both returned tables retain the original splitRevAt data and exact length
indices. The alternating recursion consumes those same halves in reverse order. -/
private def splitBackward {count : Nat} (values : { values : List Alpha // values.length = count }) :
    { values : List Alpha // values.length = count / 2 } ×
      { values : List Alpha // values.length = (count + 1) / 2 } :=
  let result := splitRevAt (count / 2) values.val
  have bounded : count / 2 ≤ values.val.length := by
    rewrite [values.property]
    exact Division.div_le_self count 2
  have lengths := splitRevAt_lengths values.val (count / 2) bounded
  (⟨result.1, lengths.1⟩, ⟨result.2, by
    apply lengths.2.trans
    rewrite [values.property]
    exact (half_lengths count).2.2⟩)

mutual
  /-- Sort the original forward table with alternating original reversed splits.

  Each retained subtype carries its exact original length. The two recursive
  calls use the original backward/forward order before the tail-recursive merge. -/
  private def forward (compare : Alpha → Alpha → Bool) :
      {count : Nat} → { values : List Alpha // values.length = count } → List Alpha
    | .zero, _ => []
    | .succ predecessor, values =>
        match predecessor, values with
        | .zero, values => values.val
        | .succ offset, values =>
            let (left, right) := splitForward values
            merge (backward compare left) (forward compare right) compare
  termination_by count _ => count
  decreasing_by all_goals first | exact (halves_lt _).1 | exact (halves_lt _).2

  /-- Sort the original reversed table with its original alternating split order.

  The retained right table is consumed backwards and the retained left table
  forwards. The supplied merge comparison resolves ties in the same original order. -/
  private def backward (compare : Alpha → Alpha → Bool) :
      {count : Nat} → { values : List Alpha // values.length = count } → List Alpha
    | .zero, _ => []
    | .succ predecessor, values =>
        match predecessor, values with
        | .zero, values => values.val
        | .succ offset, values =>
            let (left, right) := splitBackward values
            merge (backward compare right) (forward compare left) compare
  termination_by count _ => count
  decreasing_by all_goals first | exact (halves_lt _).1 | exact (halves_lt _).2
end

/-- Stably merge-sort an original finite list by its supplied Boolean comparison.

The original optimized runtime algorithm retains its alternating forward and
reversed splits, tail-recursive merge, duplicate entries and comparison order.
Equal keys retain their original order when the comparator chooses the left key.
The original list's length supplies its exact initial recursion index. -/
public def mergeSort (values : List Alpha)
    (compare : Alpha → Alpha → Bool := by exact fun left right => left ≤ right) : List Alpha :=
  forward compare ⟨values, rfl⟩

end Purelib.Data.List.Sort
