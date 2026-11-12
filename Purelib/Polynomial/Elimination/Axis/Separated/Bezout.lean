module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Constants
public import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
public import Purelib.Polynomial.Elimination.Separated.Bezout.Normalized
import Purelib.Polynomial.Elimination.Separated.Scalar

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Elimination.Separated.Bezout

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Axis.Separated.Bezout

/-- Construct the real-coordinate Bézout cofactor on a vertical line.

Add the real path components of the two normalized separated cofactors along the line through the supplied rational
abscissa. -/
def verticalBezoutLeft (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (x : Fraction.Rational) :
    (DensePolynomial Fraction.Rational) :=
  Path.Components.pathReal
      (Normalized.normalizedLeftCofactor p degreePositive x)
      (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit +
    Path.Components.pathReal
      (Normalized.normalizedRightCofactor p degreePositive x)
      (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit

/-- Construct the imaginary-coordinate Bézout cofactor on a vertical line.

Subtract the imaginary path components of the normalized right cofactor from those of the normalized left cofactor. -/
def verticalBezoutRight (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (x : Fraction.Rational) :
    (DensePolynomial Fraction.Rational) :=
  Path.Components.pathImag
      (Normalized.normalizedLeftCofactor p degreePositive x)
      (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit -
    Path.Components.pathImag
      (Normalized.normalizedRightCofactor p degreePositive x)
      (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit

/-- Certify coprimality of the real and imaginary polynomial coordinates on a vertical line.

A nonzero scalar eliminant value and a nonzero positive-degree source polynomial provide the two explicit cofactors and
their pointwise Bézout identity. -/
def verticalCoprimeCertificate (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (x : Fraction.Rational) (eliminantNonzero : (Separated.Scalar.scalarEliminant p).eval x ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Path.Components.pathReal p
        (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Path.Components.pathImag p
        (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit) where
  left := verticalBezoutLeft p degreePositive x
  right := verticalBezoutRight p degreePositive x
  identity := by
    intro y
    let point := Gaussian.Components.Basic.point x y
    have scalarNonzero := Separated.Scalar.scalar_ne_zero_of_eliminant_eval_ne_zero p x
      eliminantNonzero
    have complexIdentity := Normalized.normalizedSeparatedIdentity p nonzero
      degreePositive x scalarNonzero point
    rw [Dense.Bivariate.Gaussian.Reflection.Basic.eval_reflected,
      Dense.Bivariate.Gaussian.Lift.eval_lifted] at complexIdentity
    have reflection : Gaussian.Basic.Canonical.conj
        (2 * Gaussian.Cast.Path.ofCoordinate x - point) = point := by
      exact Affine.Axis.verticalReflection x y
    rw [reflection] at complexIdentity
    have realIdentity := congrArg Gaussian.Basic.re
      complexIdentity
    change 1 =
      (verticalBezoutLeft p degreePositive x).eval y *
          (Path.Components.pathReal p
            (Gaussian.Cast.Winding.verticalBase x)
            Gaussian.Constants.imaginaryUnit).eval y +
        (verticalBezoutRight p degreePositive x).eval y *
          (Path.Components.pathImag p
            (Gaussian.Cast.Winding.verticalBase x)
            Gaussian.Constants.imaginaryUnit).eval y
    simp only [verticalBezoutLeft,
      verticalBezoutRight, DensePolynomial.eval_add,
      DensePolynomial.eval_sub,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathImag,
      Affine.Axis.line_vertical]
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.one_re,
      Gaussian.Basic.Canonical.conj] at realIdentity
    rw [← realIdentity]
    ring1

/-- Construct the real-coordinate cofactor for a horizontal line.

Quarter-turn the nonzero positive-degree polynomial, then read the real components of its normalized separated cofactors
along the corresponding reversed vertical line. -/
def horizontalBezoutLeft (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Fraction.Rational) : (DensePolynomial Fraction.Rational) :=
  let rotated := Substitution.QuarterTurn.quarterTurn p
  let rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact degreePositive
  Path.Components.pathReal
      (Normalized.normalizedLeftCofactor rotated rotatedDegreePositive y)
      (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection +
    Path.Components.pathReal
      (Normalized.normalizedRightCofactor rotated rotatedDegreePositive y)
      (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection

/-- Construct the imaginary-coordinate cofactor for a horizontal line.

Use the difference of the normalized cofactors' imaginary components after the quarter-turn substitution, retaining the
original degree witness. -/
def horizontalBezoutRight (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Fraction.Rational) : (DensePolynomial Fraction.Rational) :=
  let rotated := Substitution.QuarterTurn.quarterTurn p
  let rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact degreePositive
  Path.Components.pathImag
      (Normalized.normalizedLeftCofactor rotated rotatedDegreePositive y)
      (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection -
    Path.Components.pathImag
      (Normalized.normalizedRightCofactor rotated rotatedDegreePositive y)
      (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection

/-- Certify coprimality of the real and imaginary polynomial coordinates on a horizontal line.

The displayed nonzero horizontal eliminant value yields the explicit quarter-turn cofactors and their exact Bézout
identity. -/
def horizontalCoprimeCertificate (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Fraction.Rational)
    (eliminantNonzero : (Eliminant.horizontalEliminant p).eval y ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Path.Components.pathReal p
        (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Path.Components.pathImag p
        (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection) := by
  let rotated := Substitution.QuarterTurn.quarterTurn p
  have rotatedNonzero : rotated.isZero = false := Substitution.QuarterTurn.quarterTurn_nonzero p nonzero
  have rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact degreePositive
  let left := Normalized.normalizedLeftCofactor rotated rotatedDegreePositive y
  let right := Normalized.normalizedRightCofactor rotated rotatedDegreePositive y
  exact
    { left := horizontalBezoutLeft p nonzero degreePositive y
      right := horizontalBezoutRight p nonzero degreePositive y
      identity := by
        intro x
        let rotatedPoint := Gaussian.Components.Basic.point y (-x)
        have scalarNonzero := Separated.Scalar.scalar_ne_zero_of_eliminant_eval_ne_zero
          rotated y eliminantNonzero
        have complexIdentity := Normalized.normalizedSeparatedIdentity rotated
          rotatedNonzero rotatedDegreePositive y scalarNonzero rotatedPoint
        rw [Dense.Bivariate.Gaussian.Reflection.Basic.eval_reflected,
          Dense.Bivariate.Gaussian.Lift.eval_lifted] at complexIdentity
        have reflection : Gaussian.Basic.Canonical.conj
            (2 * Gaussian.Cast.Path.ofCoordinate y - rotatedPoint) = rotatedPoint := by
          exact Affine.Axis.verticalReflection y (-x)
        rw [reflection, Substitution.QuarterTurn.eval_quarterTurn,
          Affine.Axis.quarterTurn_horizontalPoint] at complexIdentity
        have realIdentity := congrArg Gaussian.Basic.re
          complexIdentity
        change 1 =
          (horizontalBezoutLeft p nonzero degreePositive y).eval x *
              (Path.Components.pathReal p
                (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection).eval x +
            (horizontalBezoutRight p nonzero degreePositive y).eval x *
              (Path.Components.pathImag p
                (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection).eval x
        simp only [horizontalBezoutLeft,
          horizontalBezoutRight,
          DensePolynomial.eval_add, DensePolynomial.eval_sub,
          Path.Components.eval_pathReal,
          Path.Components.eval_pathImag,
          Affine.Axis.line_negativeVertical,
          Affine.Axis.line_horizontal]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.one_re,
          Gaussian.Basic.Canonical.conj] at realIdentity
        rw [← realIdentity]
        ring1 }

end Purelib.Polynomial.Elimination.Axis.Separated.Bezout

end
