module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks.Orientation
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Reversal
import Purelib.Tactic.Ring

/-!
# The original rational-quarter reversal on the waist

The certified original stereographic reversal identifies the third and fourth
waist charts with the reflected second and first charts. Both original chart
owners remain the indices of the resulting geometric equality.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle

/-- The original returning circuit quarter paired to a retained forward bank half. -/
@[expose] public def Half.returnQuarter : Half → Quarter.UnitCircuitQuarter
  | .first => .fourth
  | .second => .third

/-- Computed reversal identifies the original returning quarter with reflection of the original forward quarter. -/
public theorem direction_reversed (half : Half) {time : Fraction.Rational} (nonnegative : 0 ≤ time) :
    direction half.returnQuarter (Stereographic.reverseTime time) = mirror (forwardDirection half time) := by
  apply Basic.UnitVertex.eq_of_value_eq
  rewrite [direction_value]
  change Quarter.unitCircuitMultiplier half.returnQuarter *
    Stereographic.unitQuarterPoint (Stereographic.reverseTime time) =
    Data.Gaussian.Basic.conj (direction half.quarter time).value
  rewrite [direction_value]
  have readings := Stereographic.unitQuarterPoint_reverseTime_readings nonnegative
  cases half <;> apply Data.Gaussian.Basic.ext
  all_goals
    dsimp only [Half.returnQuarter, Half.quarter, Quarter.unitCircuitMultiplier,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.conj]
    rewrite [readings.1, readings.2]
    ring1

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks
