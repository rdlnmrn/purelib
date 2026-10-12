module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Geometry

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Geometry.Rational.Box.Point

/-- Degenerate rational box containing exactly the displayed rational point. -/
def pointBox (point : Data.Gaussian.Basic.Canonical) :
  Rational.Box where
  xLower := point.re
  xUpper := point.re
  yLower := point.im
  yUpper := point.im
  x_valid := le_rfl
  y_valid := le_rfl

/-- The degenerate point box contains its defining point. -/
theorem pointBox_contains (point : Data.Gaussian.Basic.Canonical) :
    (pointBox point).Contains point :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
end Purelib.Geometry.Rational.Box.Point

end
