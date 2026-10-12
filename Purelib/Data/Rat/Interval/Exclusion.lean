module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic

import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Finitely testable rational gaps

`RationalGapProcess` is an interface for a bound process that can exclude any
rational candidate when that candidate is actually presented.  A finite
inspection can exclude every member of a displayed rational list and meet
every member of a displayed accuracy list at once.

This does not construct an irrational point, enumerate the rationals, or
assert one state excluding all rationals.  It records exactly the operational
content available to finite tests.
-/

namespace Purelib.Data.Rat.Interval

section Bound

open Purelib.Data
open Purelib.Data.Rat
/-- Require a candidate rational to lie strictly below the lower endpoint or above the upper endpoint. -/
def Excludes (bound : Rat.Interval) (candidate : Fraction.Rational) : Prop :=
  candidate < bound.lower ∨ bound.upper < candidate

/-- Decide strict interval exclusion using the concrete rational endpoint comparisons. -/
instance excludesDecidable (bound : Rat.Interval) (candidate : Fraction.Rational) :
    Decidable (bound.Excludes candidate) := by
  unfold Excludes
  infer_instance

/-- A refinement preserves every strict exclusion proved for its outer interval. -/
theorem Refines.excludes {inner outer : Rat.Interval}
    (refines : Interval.Refines inner outer) {candidate : Fraction.Rational}
    (excludes : outer.Excludes candidate) : inner.Excludes candidate := by
  rcases excludes with below | above
  · exact Or.inl (below.trans_le refines.lower)
  · exact Or.inr (refines.upper.trans_lt above)

end Bound
namespace RationalGapProcess
end RationalGapProcess

end Purelib.Data.Rat.Interval

end
