module
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Geometry.Rational.Box.Basic

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Geometry.Rational.Box.Intervals

/-- The closed interval between the box imaginary-coordinate endpoints. -/
def verticalInterval (ambient : Rational.Box) :
  Data.Rat.Interval.Bounds where
  lower := ambient.yLower
  upper := ambient.yUpper
  valid := ambient.y_valid

/-- The closed interval between the box real-coordinate endpoints. -/
def horizontalInterval (ambient : Rational.Box) :
  Data.Rat.Interval.Bounds where
  lower := ambient.xLower
  upper := ambient.xUpper
  valid := ambient.x_valid
end Purelib.Geometry.Rational.Box.Intervals

end
