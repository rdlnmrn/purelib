module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters

/-- Factored coefficient in the Taylor smallness request. -/
def extractionTaylorScale : Fraction.Rational := (8
  : Fraction.Rational) * 9 * 9

/-- The unfactored Taylor coefficient used by a radius-two Newton band. -/
def extractionBandTaylorCoefficient :
  Fraction.Rational := (4 : Fraction.Rational) * 9 * 9

section
open Purelib.Polynomial in
/-- The Taylor extraction scale `8 * 9 * 9` is strictly positive. -/
public theorem
  extractionTaylorScale_pos : 0 <
  Dense.Gaussian.Newton.Box.Band.Parameters.extractionTaylorScale := by
  unfold Dense.Gaussian.Newton.Box.Band.Parameters.extractionTaylorScale
  have eightPositive := Fraction.Cast.Order.natCast_pos_direct
    (n := 8) (by decide)
  have ninePositive := Fraction.Cast.Order.natCast_pos_direct
    (n := 9) (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct eightPositive ninePositive)
    ninePositive
end

end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters

end

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
open Purelib.Polynomial in
/-- The Newton band Taylor coefficient `4 * 9 * 9` is strictly positive. -/
public theorem
  extractionBandTaylorCoefficient_pos :
    0 < Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient := by
  unfold Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient
  have fourPositive : (0 : Fraction.Rational) < 4 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide)
  have ninePositive : (0 : Fraction.Rational) < 9 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 9) (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct fourPositive ninePositive)
    ninePositive
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters

end

end
