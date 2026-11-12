module

public import Purelib.Integration.Partition.Interval.Presentation
public import Purelib.Integration.Partition.Interval.Chain

namespace Purelib.Integration.Partition.Interval.Chain.Presentation

open Purelib.Data.Rat

set_option genInjectivity false in
/-- A located failure of an exact endpoint chain.

`head` identifies a mismatched start; nested `tail` constructors retain the
original prefix, so a later `head` identifies a broken seam. `endpoint`
identifies a final endpoint mismatch, including the empty-list case. -/
public inductive Failure : Fraction.Rational → Fraction.Rational → List Interval → Type where
  /-- An empty remaining list requires equal start and finish. -/
  | endpoint {start finish : Fraction.Rational} (different : start ≠ finish) : Failure start finish []
  /-- The next retained interval does not start at the required endpoint. -/
  | head {start finish : Fraction.Rational} (interval : Interval) (tail : List Interval)
      (different : start ≠ interval.start) : Failure start finish (interval :: tail)
  /-- A failure after the retained first interval identifies a later seam or finish. -/
  | tail {start finish : Fraction.Rational} (interval : Interval) (tail : List Interval)
      (failure : Failure interval.finish finish tail) : Failure start finish (interval :: tail)

/-- Every located failure disproves the original chain predicate. -/
public theorem Failure.invalid {start finish : Fraction.Rational} {intervals : List Interval}
    (failure : Failure start finish intervals) : ¬ Chain start finish intervals := by
  induction failure with
  | endpoint different =>
      intro chain
      cases chain
      exact different rfl
  | head interval tail different =>
      intro chain
      cases interval with
      | mk first last =>
        cases chain with
        | cons rest => exact different rfl
  | tail interval tail failure inductionHypothesis =>
      intro chain
      cases interval with
      | mk first last =>
        cases chain with
        | cons rest => exact inductionHypothesis rest

set_option genInjectivity false in
/-- A finite endpoint check returns an original chain proof or a located failure. -/
public inductive Check (start finish : Fraction.Rational) (intervals : List Interval) where
  /-- The supplied list is a chain between its original endpoints. -/
  | accepted (chain : Chain start finish intervals)
  /-- The supplied endpoints or a neighboring seam do not match. -/
  | rejected (failure : Failure start finish intervals)

/-- Check exact chain incidence by structurally traversing the original interval list.

The check compares rational endpoints only. It accepts empty, reversed and
zero-length chains whenever the required endpoint equalities hold. -/
public def check (start finish : Fraction.Rational) : (intervals : List Interval) → Check start finish intervals
  | [] =>
      if equal : start = finish then
        .accepted (by cases equal; exact Chain.nil start)
      else .rejected (.endpoint equal)
  | interval :: tail =>
      if equal : start = interval.start then
        match check interval.finish finish tail with
        | .accepted rest => .accepted (by
            cases interval with
            | mk first last =>
              cases equal
              exact Chain.cons rest)
        | .rejected failure => .rejected (.tail interval tail failure)
      else .rejected (.head interval tail equal)

/-- Decide the original chain predicate using the same typed check. -/
public def recognize (start finish : Fraction.Rational) (intervals : List Interval) :
    Decidable (Chain start finish intervals) :=
  match check start finish intervals with
  | .accepted proof => .isTrue proof
  | .rejected failure => .isFalse failure.invalid

end Purelib.Integration.Partition.Interval.Chain.Presentation
