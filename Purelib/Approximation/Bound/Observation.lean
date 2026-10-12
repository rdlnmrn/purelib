module
import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.Bound.Process
import Purelib.Approximation.Observation.Basic
public import Purelib.Approximation.Observation.Interval
public import Purelib.Approximation.Observation.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Rational enclosures as finite observations

This module connects the rational-bound and neutral observation interfaces.
The symmetric rational separation is the maximum of the two directed
differences, so no absolute-value or completed metric structure is required.
-/

namespace Purelib.Approximation
namespace Bound
end Bound

namespace Observation
end Observation

namespace BoundProcess

/-- Every finite rational enclosure process is a progressive neutral observation process with the same states, requests,
and rational widths. -/
def toProgressiveObservation (process : Approximation.BoundProcess) :
    Approximation.ProgressiveObservation Fraction.Rational Distance.rationalSeparation where
  State := process.State
  observation state := (process.bound state).toObservation
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).toObservation
  accurate := process.accurate
  refinesInitial state := (process.refinesInitial state).toObservation

/-- The neutral observation theorem recovers finite pairwise separation for every rational admitted after a request. -/
theorem request_rationalSeparation_lt (process : Approximation.BoundProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {left right : Fraction.Rational}
    (leftInside :
      (process.bound (process.request state epsilon positive)).Contains left)
    (rightInside :
      (process.bound (process.request state epsilon positive)).Contains right) :
    Distance.rationalSeparation left right < epsilon :=
  process.toProgressiveObservation.request_pairwise state epsilon positive
    leftInside rightInside

end BoundProcess

end Purelib.Approximation

end
