module
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.RationalFunctions.Curve.Basic

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

section
@[expose] public section

/-!
# Canonical rational line and circle parameterizations

The CCL branch boundaries originate as coordinate lines or centered norm
circles before finite homographic pullback.  These explicit parameterizations
retain that provenance, including a proof that their parameter denominator
never vanishes.  Homographic transformation can subsequently move them into
the original polynomial coordinate.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Line

section
open Purelib.Data
section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Parameterize the vertical line with fixed real coordinate by its imaginary coordinate. -/
def realLine (threshold : Rational) :
  Curve.RationalCurve where
  numerator := ⟨[Gaussian.Constants.imaginaryUnit, Gaussian.Cast.CurveCanonical.ofCoordinate threshold]⟩
  denominator := DensePolynomial.constant 1

/-- Parameterize the horizontal line with fixed imaginary coordinate by its real coordinate. -/
def imaginaryLine (threshold : Rational) :
  Curve.RationalCurve where
  numerator := ⟨[1, Gaussian.Cast.BoundaryCanonical.imaginaryCoordinate threshold]⟩
  denominator := DensePolynomial.constant 1

end

section
open Purelib.RationalFunctions
open Purelib.Polynomial
/-- The vertical line has denominator one at every rational parameter.

The original line model retains a constant-one denominator polynomial, independently of its threshold and parameter. -/
@[simp] theorem realLine_denominatorAt
    (threshold parameter : Rational) :
    (realLine threshold).denominatorAt parameter = 1 := by
  simp only [realLine, Curve.RationalCurve.denominatorAt,
    DensePolynomial.eval_constant, -eq_self, -iff_self]
  rfl

/-- The horizontal line has denominator one at every rational parameter.

The original line model retains a constant-one denominator polynomial, independently of its threshold and parameter. -/
@[simp] theorem imaginaryLine_denominatorAt
    (threshold parameter : Rational) :
    (imaginaryLine threshold).denominatorAt parameter = 1 := by
  simp only [imaginaryLine, Curve.RationalCurve.denominatorAt,
    DensePolynomial.eval_constant, -eq_self, -iff_self]
  rfl

end

section
open Purelib.RationalFunctions
/-- The vertical line denominator is nonzero at every rational parameter. -/
theorem realLine_denominator_ne
    (threshold parameter : Rational) :
    (realLine threshold).denominatorAt parameter ≠ 0 := by
  rw [realLine_denominatorAt]
  exact Gaussian.BoundaryCanonical.one_ne_zero

/-- The horizontal line denominator is nonzero at every rational parameter. -/
theorem imaginaryLine_denominator_ne
    (threshold parameter : Rational) :
    (imaginaryLine threshold).denominatorAt parameter ≠ 0 := by
  rw [imaginaryLine_denominatorAt]
  exact Gaussian.BoundaryCanonical.one_ne_zero

end

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The vertical line numerator places the parameter in its imaginary coordinate.

The original two-coefficient Horner table retains the threshold as its real coordinate and the supplied parameter as its
imaginary coordinate. -/
@[simp] theorem realLine_numeratorAt
    (threshold parameter : Rational) :
    (realLine threshold).numeratorAt parameter = ⟨threshold, parameter⟩ := by
  apply Gaussian.Basic.ext <;>
    (simp only [Curve.RationalCurve.numeratorAt,
      realLine, Gaussian.Constants.imaginaryUnit, Gaussian.Cast.CurveCanonical.ofCoordinate,
        Gaussian.Cast.Path.ofCoordinate,
      DensePolynomial.eval, DensePolynomial.evalCoeffs,
      List.foldl_cons, List.foldl_nil, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
      mul_zero, zero_mul, one_mul, add_zero, zero_add, sub_self, -eq_self, -iff_self]
     rfl)

/-- The horizontal line numerator places the parameter in its real coordinate.

The original two-coefficient Horner table retains the supplied parameter as its real coordinate and the threshold as its
imaginary coordinate. -/
@[simp] theorem imaginaryLine_numeratorAt
    (threshold parameter : Rational) :
    (imaginaryLine threshold).numeratorAt parameter = ⟨parameter, threshold⟩ := by
  apply Gaussian.Basic.ext <;>
    (simp only [Curve.RationalCurve.numeratorAt,
      imaginaryLine, Gaussian.Cast.BoundaryCanonical.imaginaryCoordinate,
        Gaussian.Cast.Path.ofCoordinate,
      DensePolynomial.eval, DensePolynomial.evalCoeffs,
      List.foldl_cons, List.foldl_nil, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      zero_mul, one_mul, add_zero, zero_add, -eq_self, -iff_self]
     rfl)

end

open Purelib.RationalFunctions
/-- The vertical line point has the fixed threshold and the supplied imaginary parameter. -/
@[simp] theorem realLine_point
    (threshold parameter : Rational) :
    (realLine threshold).point parameter = ⟨threshold, parameter⟩ := by
  rw [Curve.RationalCurve.point,
    realLine_numeratorAt, realLine_denominatorAt]
  have inverseOne : (1 : Gaussian.Basic.Canonical)⁻¹ = 1 :=
    Gaussian.Field.inv_one_direct
  rw [inverseOne,
    Gaussian.Basic.mul_one]

/-- The horizontal line point has the fixed threshold and the supplied real parameter. -/
@[simp] theorem imaginaryLine_point
    (threshold parameter : Rational) :
    (imaginaryLine threshold).point parameter = ⟨parameter, threshold⟩ := by
  rw [Curve.RationalCurve.point,
    imaginaryLine_numeratorAt, imaginaryLine_denominatorAt]
  have inverseOne : (1 : Gaussian.Basic.Canonical)⁻¹ = 1 :=
    Gaussian.Field.inv_one_direct
  rw [inverseOne,
    Gaussian.Basic.mul_one]

/-- The vertical line parameterization is injective because its imaginary coordinate is the parameter. -/
theorem realLine_point_injective (threshold :
  Rational) :
    Function.Injective (realLine threshold).point := by
  intro left right equal
  have imaginary := congrArg Gaussian.Basic.im equal
  simpa only [realLine_point] using imaginary

/-- The horizontal line parameterization is injective because its real coordinate is the parameter. -/
theorem imaginaryLine_point_injective (threshold :
  Rational) :
    Function.Injective (imaginaryLine threshold).point := by
  intro left right equal
  have real := congrArg Gaussian.Basic.re equal
  simpa only [imaginaryLine_point] using real
end

end Purelib.RationalFunctions.Curve.Canonical.Line

end
