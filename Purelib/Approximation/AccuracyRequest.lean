module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite batches of arbitrary-accuracy requests

This module isolates a useful replacement for an appeal to an infinite
limit: every displayed finite list of positive rational demands has one
explicit final state satisfying all of them.  Preservation comes from finite
refinement, not compactness or a completed intersection.
-/

namespace Purelib.Approximation

set_option genInjectivity false in
/-- One positive rational accuracy demand. -/
structure AccuracyRequest where
  /-- The retained rational tolerance of this request. -/ tolerance : Fraction.Rational
  /-- The requested tolerance is strictly positive. -/ positive : 0 < tolerance
deriving @[expose] DecidableEq

constructive_injectivity AccuracyRequest

namespace AccuracyRequest

/-- Equal retained tolerances identify the original positive accuracy requests. -/
theorem eq_of_tolerance_eq {first last : AccuracyRequest}
    (equal : first.tolerance = last.tolerance) : first = last := by
  cases first with
  | mk first firstPositive =>
    cases last with
    | mk last lastPositive =>
      change first = last at equal
      cases equal
      rfl

/-- The smaller of two actual positive accuracy demands pays both original requests. -/
def minimum (first last : AccuracyRequest) : AccuracyRequest :=
  ⟨min first.tolerance last.tolerance, Fraction.Order.Basic.lt_min first.positive last.positive⟩

/-- The computed common accuracy pays its original left request. -/
theorem minimum_le_left (first last : AccuracyRequest) : (first.minimum last).tolerance ≤ first.tolerance :=
  Fraction.Order.Basic.min_le_left _ _

/-- The same common accuracy also pays the independent original right request. -/
theorem minimum_le_right (first last : AccuracyRequest) : (first.minimum last).tolerance ≤ last.tolerance :=
  Fraction.Order.Basic.min_le_right _ _

end AccuracyRequest

namespace BoundProcess
end BoundProcess

namespace ProgressiveObservation
end ProgressiveObservation

end Purelib.Approximation

end
