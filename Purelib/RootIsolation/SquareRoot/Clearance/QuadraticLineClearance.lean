module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Algebra.Group.Negation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Track.Accelerated
import Purelib.RootIsolation.Track.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.SquareRootDegree
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Bounds.Square

/-!
# Direct finite quadratic line clearances

The short resultant formulas are independent of continuation owners.  Keeping
them below continuation lets every quadratic checked-Newton consumer build
its certified line bounds without the general polynomial Bézout majorant.
These are the existing direct bounds, with their finite algebraic proofs;
no generated coefficients or concrete period certificates are imported.
-/

namespace Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RootIsolation.SquareRoot.Clearance
open Purelib.Riemann.RootContinuation

/-- The rational coordinate type of the retained quadratic owner boxes. -/
public abbrev Coordinate := Fraction.Rational
/-- The canonical Gaussian rational parameter type. -/
public abbrev Gaussian := Gaussian.Basic.Canonical
/-- The dense Gaussian polynomial type used for the quadratic root equation. -/
public abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The rational box type used by the original quadratic clearance certificates. -/
public abbrev Box := Purelib.Geometry.Rational.Box

/-- The squared rational two-coordinate scalar product is bounded by the product of the two squared norms.

The difference between the right and left sides is the square of the
two-coordinate alternating product, evaluated on the supplied rational inputs. -/
private theorem sum_product_sq_le_product_sums
    (a b first second : Coordinate) :
    (a * first + b * second) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (first ^ 2 + second ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a * second - b * first) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (first ^ 2 + second ^ 2) -
          (a * first + b * second) ^ 2 := by
      ring1

/-- A positive coefficient majorant for the retained constant and linear factors.

The exact rational maximum retains one as a positive floor and bounds the
coefficient squares on the supplied coordinate-square radius. -/
@[expose] public def directLineMajorant
    (constant slope intercept radiusSq : Coordinate) : Fraction.Rational :=
  max 1 (constant ^ 2 + 2 * (slope ^ 2 * radiusSq + intercept ^ 2))

/-- The computed rational line majorant is strictly positive.

The retained maximum is at least its first argument, the positive rational
one, independently of the supplied coefficient values. -/
public theorem directLineMajorant_positive
    (constant slope intercept radiusSq : Coordinate) :
    0 < directLineMajorant constant slope intercept radiusSq :=
  (show (0 : Coordinate) < 1 by decide).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- The rational resultant identity gives a norm-square lower bound.

A squared-coordinate bound controls the retained linear factor. The finite
two-coordinate scalar-product bound then gives the displayed positive-denominator quotient. -/
private theorem directLineLower
    (coordinate radiusSq constant slope intercept determinant
      realPart imaginaryPart : Coordinate)
    (coordinateSq : coordinate ^ 2 ≤ radiusSq)
    (identity : determinant =
      constant * realPart + (slope * coordinate + intercept) * imaginaryPart) :
    determinant ^ 2 /
        directLineMajorant constant slope intercept radiusSq ≤
      realPart ^ 2 + imaginaryPart ^ 2 := by
  let linear := slope * coordinate + intercept
  let coefficientSq := constant ^ 2 + linear ^ 2
  let valueSq := realPart ^ 2 + imaginaryPart ^ 2
  have productLe : slope ^ 2 * coordinate ^ 2 ≤
      slope ^ 2 * radiusSq :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coordinateSq
      (Fraction.Order.Arithmetic.sq_nonneg_direct slope)
  have linearSqLe : linear ^ 2 ≤
      2 * (slope ^ 2 * radiusSq + intercept ^ 2) := by
    calc
      linear ^ 2 ≤
          2 * ((slope * coordinate) ^ 2 + intercept ^ 2) := by
        exact Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
      _ = 2 * (slope ^ 2 * coordinate ^ 2 + intercept ^ 2) := by
        ring1
      _ ≤ 2 * (slope ^ 2 * radiusSq + intercept ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct productLe
            (Fraction.Order.Basic.le_refl _)) (by decide)
  have coefficientLe : coefficientSq ≤
      directLineMajorant constant slope intercept radiusSq :=
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl _) linearSqLe).trans (Fraction.Order.Basic.le_max_right _ _)
  have valueNonnegative : 0 ≤ valueSq :=
    calc
      0 = (0 : Coordinate) + 0 := (Fraction.zero_add 0).symm
      _ ≤ valueSq := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have cauchy : determinant ^ 2 ≤ coefficientSq * valueSq := by
    calc
      determinant ^ 2 =
          (constant * realPart + linear * imaginaryPart) ^ 2 := by
        rw [identity]
      _ ≤ coefficientSq * valueSq :=
        sum_product_sq_le_product_sums _ _ _ _
  have scaled : determinant ^ 2 ≤
      directLineMajorant constant slope intercept radiusSq * valueSq :=
    cauchy.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe valueNonnegative)
  apply (Fraction.Order.Field.div_le_iff_pos
    (directLineMajorant_positive constant slope intercept radiusSq)).mpr
  rw [Fraction.Field.mul_comm]
  exact scaled

/-- The exact lower bound on one vertical side of a quadratic owner box.

The numerator is the retained vertical determinant square. Its denominator
uses the original constant and linear factors and endpoint square maximum. -/
@[expose] public def directVerticalClearanceBound (parameter : Gaussian) (box : Box)
    (x : Coordinate) : Fraction.Rational :=
  QuadraticAxisElimination.verticalDeterminant
      parameter x ^ 2 /
    directLineMajorant (4 * x ^ 2) (2 * x) parameter.im
      (max (box.yLower ^ 2) (box.yUpper ^ 2))

/-- Direct exact clearance on one vertical side of a quadratic owner box.

The bound retains the original vertical determinant square and coefficient
majorant. Nonvanishing makes the exact quotient positive on the retained box side. -/
@[expose] public def directVerticalClearance (parameter : Gaussian) (box : Box)
    (x : Coordinate)
    (determinantNonzero :
      QuadraticAxisElimination.verticalDeterminant
        parameter x ≠ 0) :
    Clearance.Box.Line.Basic.VerticalLineClearance (QuadraticAxisElimination.rootPolynomial parameter) box x where
  bound := directVerticalClearanceBound parameter box x
  positive := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.exact_rational_sq_pos determinantNonzero)
    (directLineMajorant_positive _ _ _ _)
  lower := by
    intro y lower upper
    let determinant :=
      QuadraticAxisElimination.verticalDeterminant
        parameter x
    let realPart := x ^ 2 - y ^ 2 - parameter.re
    let imaginaryPart := 2 * x * y - parameter.im
    have coordinateSq : y ^ 2 ≤
        max (box.yLower ^ 2) (box.yUpper ^ 2) :=
      Purelib.Geometry.Rational.Box.sq_le_endpoint_max lower upper
    have identity : determinant =
        (4 * x ^ 2) * realPart +
          ((2 * x) * y + parameter.im) * imaginaryPart := by
      dsimp only [determinant, realPart, imaginaryPart,
        QuadraticAxisElimination.verticalDeterminant]
      ring1
    have direct := directLineLower y
      (max (box.yLower ^ 2) (box.yUpper ^ 2))
      (4 * x ^ 2) (2 * x) parameter.im determinant realPart imaginaryPart
        coordinateSq identity
    have evaluation :
        Data.Gaussian.Norm.Basic.normSq
            ((QuadraticAxisElimination.rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) =
          (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
            (2 * x * y - parameter.im) ^ 2 := by
      rewrite [QuadraticAxisElimination.rootPolynomial, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
        SquareRootDegree.degreeTwo_value, pow_two]
      change ((x * x - y * y) - parameter.re) ^ 2 +
        ((x * y + y * x) - parameter.im) ^ 2 =
        (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
        (2 * x * y - parameter.im) ^ 2
      ring1
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical, evaluation]
    dsimp only [determinant, realPart, imaginaryPart] at direct
    exact direct

/-- The executable lower bound used on one horizontal side of a quadratic
owner box.

The numerator is the retained horizontal determinant square. The denominator
uses the original horizontal Bézout coefficient signs and endpoint square maximum. -/
@[expose] public def directHorizontalClearanceBound (parameter : Gaussian) (box : Box)
    (y : Coordinate) : Fraction.Rational :=
  QuadraticAxisElimination.horizontalDeterminant
      parameter y ^ 2 /
    directLineMajorant (4 * y ^ 2) (-(2 * y)) (-parameter.im)
      (max (box.xLower ^ 2) (box.xUpper ^ 2))

/-- Direct exact clearance on one horizontal side of a quadratic owner box.

The bound retains the original horizontal determinant square and coefficient
majorant. Nonvanishing makes the exact quotient positive on the retained box side. -/
@[expose] public def directHorizontalClearance (parameter : Gaussian) (box : Box)
    (y : Coordinate)
    (determinantNonzero :
      QuadraticAxisElimination.horizontalDeterminant
        parameter y ≠ 0) :
    Clearance.Box.Line.Basic.HorizontalLineClearance (QuadraticAxisElimination.rootPolynomial parameter) box y where
  bound := directHorizontalClearanceBound parameter box y
  positive := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.exact_rational_sq_pos determinantNonzero)
    (directLineMajorant_positive _ _ _ _)
  lower := by
    intro x lower upper
    let determinant :=
      QuadraticAxisElimination.horizontalDeterminant
        parameter y
    let realPart := x ^ 2 - y ^ 2 - parameter.re
    let imaginaryPart := 2 * x * y - parameter.im
    have coordinateSq : x ^ 2 ≤
        max (box.xLower ^ 2) (box.xUpper ^ 2) :=
      Purelib.Geometry.Rational.Box.sq_le_endpoint_max lower upper
    have identity : determinant =
        (4 * y ^ 2) * realPart +
          ((-(2 * y)) * x + (-parameter.im)) * imaginaryPart := by
      dsimp only [determinant, realPart, imaginaryPart,
        QuadraticAxisElimination.horizontalDeterminant]
      ring1
    have direct := directLineLower x
      (max (box.xLower ^ 2) (box.xUpper ^ 2))
      (4 * y ^ 2) (-(2 * y)) (-parameter.im) determinant realPart
        imaginaryPart coordinateSq identity
    have evaluation :
        Data.Gaussian.Norm.Basic.normSq
            ((QuadraticAxisElimination.rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) =
          (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
            (2 * x * y - parameter.im) ^ 2 := by
      rewrite [QuadraticAxisElimination.rootPolynomial, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
        SquareRootDegree.degreeTwo_value, pow_two]
      change ((x * x - y * y) - parameter.re) ^ 2 +
        ((x * y + y * x) - parameter.im) ^ 2 =
        (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
        (2 * x * y - parameter.im) ^ 2
      ring1
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical, evaluation]
    dsimp only [determinant, realPart, imaginaryPart] at direct
    exact direct

end Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

namespace Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.Owner

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RootIsolation.SquareRoot.Clearance
open Purelib.Riemann.RootContinuation

/-- Vertical and horizontal line clearances for the quadratic axis eliminants.

Each supplied nonzero eliminant value is transported to its retained
resultant, producing the original exact side-clearance certificate. -/
@[expose] public def quadraticAxisClearances
    (parameter : Gaussian.Basic.Canonical) :
    Clearance.Box.Line.Elimination.Provider.AxisClearances (QuadraticAxisElimination.quadraticAxisElimination parameter)
      where
  vertical ambient x nonzero :=
    ExactQuadraticOwnerClearance.directVerticalClearance
      parameter ambient x (by
        simpa only [QuadraticAxisElimination.quadraticAxisElimination,
          QuadraticAxisElimination.quadraticVerticalEliminant_eval] using nonzero)
  horizontal ambient y nonzero :=
    ExactQuadraticOwnerClearance.directHorizontalClearance
      parameter ambient y (by
        simpa only [QuadraticAxisElimination.quadraticAxisElimination,
          QuadraticAxisElimination.quadraticHorizontalEliminant_eval] using nonzero)

/-- Accelerate a quadratic winding-one track with its retained axis clearances.

The original finite checked-Newton rule is attempted before total refinement.
The original initial state and fallback remain part of the retained track. -/
@[expose] public def accelerateTrack (parameter : Gaussian.Basic.Canonical)
    {ambient : Box}
    (track : Track.Basic.WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) ambient) :
    Track.Basic.WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) ambient :=
  Track.Accelerated.accelerate (QuadraticAxisElimination.quadraticAxisElimination parameter) track
    (quadraticAxisClearances parameter)

/-- Quadratic checked-Newton acceleration retains the original track's initial state exactly. -/
@[simp] public theorem accelerateTrack_initial (parameter : Gaussian.Basic.Canonical)
    {ambient : Box}
    (track : Track.Basic.WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) ambient) :
    (accelerateTrack parameter track).initial = track.initial := by
  dsimp only [accelerateTrack, Track.Accelerated.accelerate]

end Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.Owner
