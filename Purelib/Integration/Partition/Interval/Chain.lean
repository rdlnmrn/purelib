module

public import Purelib.Integration.Partition.Interval

/-!
# Exact readbacks of retained endpoint chains

Composition keeps both original interval lists. Bounded coordinate readbacks
recover the original outer endpoints and every displayed neighboring seam.
-/

public section

namespace Purelib.Integration.Partition.Interval.Chain

open Purelib.Data.Rat

/-- Compose exact endpoint chains by concatenating their original interval lists.

The first finish must be the second start. Structural recursion retains each
original interval and proves the same endpoint incidence on the combined list.
-/
theorem append {start middle finish : Fraction.Rational} {first second : List Interval}
    : Chain start middle first → Chain middle finish second → Chain start finish (first ++ second)
  | .nil _, right => right
  | .cons rest, right => .cons (append rest right)

/-- The first interval in a nonempty retained chain starts at its original start. -/
theorem start_eq {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) (bound : 0 < intervals.length) :
    (intervals[0]'bound).start = start := by
  cases chain with
  | nil => cases bound
  | cons rest => rfl

/-- Every two neighboring original bounded intervals share their exact endpoint.

The supplied bounds identify consecutive occurrences in the retained list.
Structural induction follows those same occurrences without selecting a new list.
-/
theorem adjacent {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) (index : Nat)
    (bound : index < intervals.length) (nextBound : index + 1 < intervals.length) :
    (intervals[index]'bound).finish = (intervals[index + 1]'nextBound).start := by
  induction chain generalizing index with
  | nil => cases bound
  | cons rest retained =>
      cases index with
      | zero =>
          cases rest with
          | nil => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ nextBound)).elim
          | cons remaining => rfl
      | succ index =>
          exact retained index (Nat.lt_of_succ_lt_succ bound)
            (Nat.lt_of_succ_lt_succ nextBound)

/-- The final bounded interval finishes at the original finish of the retained chain.

The displayed successor equation proves this is the last original occurrence.
Structural induction retains its coordinate and the same finishing endpoint.
-/
theorem finish_eq {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) (index : Nat)
    (bound : index < intervals.length) (last : index + 1 = intervals.length) :
    (intervals[index]'bound).finish = finish := by
  induction chain generalizing index with
  | nil => cases bound
  | @cons start middle finish tail rest retained =>
      cases index with
      | zero =>
          have empty : tail.length = 0 := (Nat.succ.inj last).symm
          cases tail with
          | nil => cases rest; rfl
          | cons first remaining => cases empty
      | succ index =>
          exact retained index (Nat.lt_of_succ_lt_succ bound) (Nat.succ.inj last)

end Purelib.Integration.Partition.Interval.Chain

end
