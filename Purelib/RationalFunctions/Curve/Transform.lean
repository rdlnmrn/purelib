module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Inverse
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.RationalFunctions.Curve.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite rational curves and denominator-cleared polynomial evaluation

A rationally parameterized Gaussian curve is represented by two finite dense
Gaussian polynomials `N(t)` and `D(t)`.  Evaluation means `N(t) / D(t)` only
at an explicitly supplied nonzero denominator.  A Horner fold computes
`D(t)^n p(N(t)/D(t))` without division; its real and imaginary coefficient
polynomials are therefore suitable for finite gcd and Sturm calculations.
-/

namespace Purelib.RationalFunctions.Curve

/- The doubled public name `Purelib.CCL.Boundary.Curve.Rational.RationalCurve` is intentional:
the outer component names the module and the inner component names its main
finite data type. -/
namespace RationalCurve

open Purelib.LinearAlgebra in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Apply a Gaussian matrix homography to the curve's homogeneous polynomial pair.

Each new coordinate is the corresponding matrix row applied to the original numerator and denominator polynomials. The
construction requires no affine denominator decision. -/
def transform (matrix :
  Coordinates2.Matrix.GaussianMatrix) (curve : Curve.RationalCurve) : Curve.RationalCurve where
  numerator := Dense.Basic.DensePolynomial.scale matrix.a curve.numerator +
    Dense.Basic.DensePolynomial.scale matrix.b curve.denominator
  denominator := Dense.Basic.DensePolynomial.scale matrix.c curve.numerator +
    Dense.Basic.DensePolynomial.scale matrix.d curve.denominator

section
open Purelib.LinearAlgebra
open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The transformed numerator evaluates to the first matrix row applied to the original coordinate values. -/
@[simp] theorem numeratorAt_transform
    (matrix : Coordinates2.Matrix.GaussianMatrix) (curve : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational) :
    (curve.transform matrix).numeratorAt parameter =
      matrix.a * curve.numeratorAt parameter +
        matrix.b * curve.denominatorAt parameter := by
  simp only [Curve.RationalCurve.transform, Curve.RationalCurve.numeratorAt, Dense.Basic.DensePolynomial.eval_add,
    Dense.Basic.DensePolynomial.eval_scale]
  rfl

/-- The transformed denominator evaluates to the second matrix row applied to the original coordinate values. -/
@[simp] theorem denominatorAt_transform
    (matrix : Coordinates2.Matrix.GaussianMatrix) (curve : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational) :
    (curve.transform matrix).denominatorAt parameter =
      matrix.c * curve.numeratorAt parameter +
        matrix.d * curve.denominatorAt parameter := by
  simp only [Curve.RationalCurve.transform, Curve.RationalCurve.denominatorAt, Dense.Basic.DensePolynomial.eval_add,
    Dense.Basic.DensePolynomial.eval_scale]
  rfl

end

open Purelib.LinearAlgebra
open Purelib.Data
open Purelib.Geometry
open Purelib.RationalFunctions
/-- At a nonzero curve denominator, the transformed denominator factors through the affine homography denominator. -/
theorem denominatorAt_transform_eq
    (matrix : Coordinates2.Matrix.GaussianMatrix) (curve : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (curve.transform matrix).denominatorAt parameter =
      Projective.Homography.Basic.denominator matrix (curve.point parameter) *
        curve.denominatorAt parameter := by
  rw [Curve.RationalCurve.denominatorAt_transform,
    curve.numeratorAt_eq_point_mul_denominatorAt parameter
      denominatorNonzero]
  unfold Projective.Homography.Basic.denominator
  ring1

/-- Homogeneous transformation agrees with affine homographic evaluation where both denominators are nonzero.

The original curve denominator and the matrix denominator at the affine point are explicit premises. Their product is
the transformed homogeneous denominator. -/
theorem point_transform
    (matrix : Coordinates2.Matrix.GaussianMatrix) (curve : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational)
    (curveDenominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (matrixDenominatorNonzero :
      Projective.Homography.Basic.denominator matrix (curve.point parameter) ≠
        0) :
    (curve.transform matrix).point parameter =
      Projective.Homography.Basic.homographic matrix (curve.point parameter) := by
  have transformedDenominator :
      (curve.transform matrix).denominatorAt parameter =
        Projective.Homography.Basic.denominator matrix
            (curve.point parameter) * curve.denominatorAt parameter :=
    Curve.RationalCurve.denominatorAt_transform_eq matrix curve parameter
      curveDenominatorNonzero
  have transformedDenominatorNonzero :
      (curve.transform matrix).denominatorAt parameter ≠ 0 := by
    rw [transformedDenominator]
    exact Gaussian.Field.mul_ne_zero_direct
      matrixDenominatorNonzero curveDenominatorNonzero
  apply Gaussian.Field.mul_right_cancel_of_ne
    transformedDenominatorNonzero
  calc
    (curve.transform matrix).point parameter *
        (curve.transform matrix).denominatorAt parameter =
      (curve.transform matrix).numeratorAt parameter := by
        unfold Curve.RationalCurve.point
        rw [Gaussian.Basic.mul_assoc]
        rw [Gaussian.Basic.Canonical.inv_mul_cancel _
            transformedDenominatorNonzero,
          Gaussian.Basic.mul_one]
    _ = Projective.Homography.Basic.numerator matrix (curve.point parameter) *
        curve.denominatorAt parameter := by
      rw [Curve.RationalCurve.numeratorAt_transform,
        curve.numeratorAt_eq_point_mul_denominatorAt parameter
          curveDenominatorNonzero]
      unfold Projective.Homography.Basic.numerator
      calc
        matrix.a *
              (curve.point parameter * curve.denominatorAt parameter) +
            matrix.b * curve.denominatorAt parameter =
          (matrix.a * curve.point parameter) *
              curve.denominatorAt parameter +
            matrix.b * curve.denominatorAt parameter := by
          rw [Gaussian.Basic.mul_assoc]
        _ = (matrix.a * curve.point parameter + matrix.b) *
              curve.denominatorAt parameter :=
          (Gaussian.Basic.right_distrib _ _ _).symm
    _ = Projective.Homography.Basic.homographic matrix
          (curve.point parameter) *
        (curve.transform matrix).denominatorAt parameter := by
      rw [transformedDenominator]
      unfold Projective.Homography.Basic.homographic
      let numerator := Projective.Homography.Basic.numerator matrix (curve.point parameter)
      let denominator :=
        Projective.Homography.Basic.denominator matrix (curve.point parameter)
      let curveDenominator := curve.denominatorAt parameter
      change numerator * curveDenominator =
        (numerator * denominator⁻¹) * (denominator * curveDenominator)
      calc
        numerator * curveDenominator =
            numerator * 1 * curveDenominator := by
          rw [Gaussian.Basic.mul_one]
        _ = numerator * (denominator⁻¹ * denominator) *
            curveDenominator := by
          rw [Gaussian.Basic.Canonical.inv_mul_cancel denominator
            matrixDenominatorNonzero]
        _ = numerator * ((denominator⁻¹ * denominator) *
            curveDenominator) :=
          Gaussian.Basic.mul_assoc _ _ _
        _ = numerator * (denominator⁻¹ *
            (denominator * curveDenominator)) := by
          rw [Gaussian.Basic.mul_assoc]
        _ = (numerator * denominator⁻¹) *
            (denominator * curveDenominator) :=
          (Gaussian.Basic.mul_assoc _ _ _).symm

end RationalCurve
end Purelib.RationalFunctions.Curve

end

section
@[expose] public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.RationalFunctions.Curve
namespace NondegenerateHelpers

open Purelib.LinearAlgebra in
open Purelib.Data in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- The adjugate-transformed denominator factors through the original nonzero curve denominator. -/
public theorem transformedDenominator_eq
    (matrix : Coordinates2.Matrix.GaussianMatrix) (source : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0) :
    (source.transform
      (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)).denominatorAt parameter =
        Projective.Homography.Basic.denominator
            (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)
            (source.point parameter) * source.denominatorAt parameter :=
  Curve.RationalCurve.denominatorAt_transform_eq
    (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix) source parameter
      sourceDenominatorNonzero

end NondegenerateHelpers
open Purelib.LinearAlgebra in
open Purelib.Data in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Nonzero original and adjugate-transformed curve denominators imply a nonzero affine adjugate denominator. -/
public theorem adjugateDenominator_ne_of_transformed
    (matrix : Coordinates2.Matrix.GaussianMatrix) (source : Curve.RationalCurve) (parameter :
      Rat.Fraction.Rational)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (transformedDenominatorNonzero :
      (source.transform
        (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)).denominatorAt
          parameter ≠ 0) :
    Projective.Homography.Basic.denominator
        (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)
        (source.point parameter) ≠ 0 := by
  intro zero
  apply transformedDenominatorNonzero
  rw [Curve.NondegenerateHelpers.transformedDenominator_eq matrix source parameter
    sourceDenominatorNonzero, zero,
    Gaussian.Basic.zero_mul]

end Purelib.RationalFunctions.Curve

end

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.RationalFunctions.Curve

open Purelib.LinearAlgebra in
open Purelib.Data in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Pulling a homographic image back by the adjugate recovers its original affine point.

The matrix determinant, original matrix denominator and source curve denominator are nonzero. The supplied source-point
identity yields both nonzeroness of the transformed curve denominator and equality of its point to the original value.
-/
theorem inverseTransform_point
    (matrix : Coordinates2.Matrix.GaussianMatrix)
    (determinantNonzero :
      Coordinates2.Matrix.BoundaryAdjugate.determinant matrix ≠ 0)
    (source : Curve.RationalCurve) (parameter : Rat.Fraction.Rational)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (value : Gaussian.Basic.Canonical)
    (matrixDenominatorNonzero :
      Projective.Homography.Basic.denominator matrix value ≠ 0)
    (sourcePoint : source.point parameter =
      Projective.Homography.Basic.homographic matrix value) :
    let transformed := source.transform
      (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)
    transformed.denominatorAt parameter ≠ 0 ∧
      transformed.point parameter = value := by
  let inverse := Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix
  let transformed := source.transform inverse
  have inverseDenominatorNonzero :
      Projective.Homography.Basic.denominator inverse
        (source.point parameter) ≠ 0 := by
    rw [sourcePoint]
    exact Projective.Homography.adjugate_denominator_homographic_ne
      matrix value determinantNonzero matrixDenominatorNonzero
  have transformedDenominatorNonzero :
      transformed.denominatorAt parameter ≠ 0 := by
    rw [Curve.RationalCurve.denominatorAt_transform_eq
      inverse source parameter sourceDenominatorNonzero]
    exact Gaussian.Field.mul_ne_zero_direct
      inverseDenominatorNonzero sourceDenominatorNonzero
  refine ⟨transformedDenominatorNonzero, ?_⟩
  calc
    transformed.point parameter =
        Projective.Homography.Basic.homographic inverse
          (source.point parameter) :=
      Curve.RationalCurve.point_transform
        inverse source parameter sourceDenominatorNonzero
          inverseDenominatorNonzero
    _ = Projective.Homography.Basic.homographic inverse
        (Projective.Homography.Basic.homographic matrix value) := by
      rw [sourcePoint]
    _ = value :=
      Projective.Homography.homographic_adjugate_forward_inverse
        matrix value determinantNonzero matrixDenominatorNonzero
end Purelib.RationalFunctions.Curve

end
