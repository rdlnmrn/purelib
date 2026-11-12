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
public import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Elimination.Separated.Bezout.Prepared
import Purelib.Polynomial.Elimination.Separated.Preparation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Axis.Separated.Prepared

open Purelib.Polynomial.Elimination.Separated.Preparation (Prepared)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Elimination.Separated.Bezout.Prepared

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-- Certify coprimality of the real and imaginary polynomial coordinates on a vertical line.

A nonzero scalar eliminant value and a nonzero positive-degree source polynomial provide the two explicit cofactors and
their pointwise Bézout identity. -/
@[expose] def vertical {p : CoefficientPolynomial} (prepared : Prepared p)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (x : Fraction.Rational) (eliminantNonzero : prepared.eliminant.eval x ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Path.Components.pathReal p
        (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Path.Components.pathImag p
        (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit) :=
  let cofactors := normalizedCofactors prepared degreePositive x
  let left := Path.Components.pathParts cofactors.1
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  let right := Path.Components.pathParts cofactors.2
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  { left := left.1 + right.1
    right := left.2 - right.2
    identity := by
      intro y
      let point := Gaussian.Components.Basic.point x y
      have scalarNonzero := prepared.scalar_ne_zero x
        eliminantNonzero
      have complexIdentity := normalizedIdentity prepared nonzero
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
        (Path.Components.pathReal (normalizedLeft prepared degreePositive x) (Gaussian.Cast.Winding.verticalBase x)
            Gaussian.Constants.imaginaryUnit + Path.Components.pathReal (normalizedRight prepared degreePositive x)
            (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit).eval y *
            (Path.Components.pathReal p
              (Gaussian.Cast.Winding.verticalBase x)
              Gaussian.Constants.imaginaryUnit).eval y +
          (Path.Components.pathImag (normalizedLeft prepared degreePositive x) (Gaussian.Cast.Winding.verticalBase
              x) Gaussian.Constants.imaginaryUnit - Path.Components.pathImag (normalizedRight prepared
              degreePositive x) (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit).eval y *
            (Path.Components.pathImag p
              (Gaussian.Cast.Winding.verticalBase x)
              Gaussian.Constants.imaginaryUnit).eval y
      simp only [DensePolynomial.eval_add,
        DensePolynomial.eval_sub,
        Path.Components.eval_pathReal,
        Path.Components.eval_pathImag,
        Affine.Axis.line_vertical]
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.one_re,
        Gaussian.Basic.Canonical.conj] at realIdentity
      rw [← realIdentity]
      ring1 }

/-- Certify coprimality of the real and imaginary polynomial coordinates on a horizontal line.

The displayed nonzero horizontal eliminant value yields the explicit quarter-turn cofactors and their exact Bézout
identity. -/
@[expose] def horizontal {p : CoefficientPolynomial}
    (prepared : Prepared (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Fraction.Rational)
    (eliminantNonzero : prepared.eliminant.eval y ≠ 0) :
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
  let cofactors := normalizedCofactors prepared rotatedDegreePositive y
  let left := Path.Components.pathParts cofactors.1
    (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
  let right := Path.Components.pathParts cofactors.2
    (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
  exact
    { left := left.1 + right.1
      right := left.2 - right.2
      identity := by
        intro x
        let rotatedPoint := Gaussian.Components.Basic.point y (-x)
        have scalarNonzero := prepared.scalar_ne_zero y eliminantNonzero
        have complexIdentity := normalizedIdentity prepared
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
          (Path.Components.pathReal (normalizedLeft prepared rotatedDegreePositive y)
              (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection +
              Path.Components.pathReal (normalizedRight prepared rotatedDegreePositive y)
              (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection).eval x *
              (Path.Components.pathReal p
                (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection).eval x +
            (Path.Components.pathImag (normalizedLeft prepared rotatedDegreePositive y)
                (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection -
                Path.Components.pathImag (normalizedRight prepared rotatedDegreePositive y)
                (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection).eval x *
              (Path.Components.pathImag p
                (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection).eval x
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_sub,
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

/-- The cached vertical real cofactor is the same original polynomial on every retained preparation. -/
theorem vertical_left {p : CoefficientPolynomial} (prepared : Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    (vertical prepared nonzero positive parameter safe).left =
      Path.Components.pathReal (normalizedLeft prepared positive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit +
      Path.Components.pathReal (normalizedRight prepared positive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit := rfl

/-- The cached vertical imaginary cofactor is the same original polynomial on every retained preparation. -/
theorem vertical_right {p : CoefficientPolynomial} (prepared : Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    (vertical prepared nonzero positive parameter safe).right =
      Path.Components.pathImag (normalizedLeft prepared positive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit -
      Path.Components.pathImag (normalizedRight prepared positive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit := rfl

/-- The cached horizontal real cofactor is the same original quarter-turned polynomial on every input. -/
theorem horizontal_left {p : CoefficientPolynomial}
    (prepared : Prepared (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    let rotatedPositive : 0 < (Substitution.QuarterTurn.quarterTurn p).natDegree := by
      rewrite [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
      exact positive
    (horizontal prepared nonzero positive parameter safe).left =
      Path.Components.pathReal (normalizedLeft prepared rotatedPositive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection +
      Path.Components.pathReal (normalizedRight prepared rotatedPositive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection := rfl

/-- The cached horizontal imaginary cofactor is the same original quarter-turned polynomial on every input. -/
theorem horizontal_right {p : CoefficientPolynomial}
    (prepared : Prepared (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    let rotatedPositive : 0 < (Substitution.QuarterTurn.quarterTurn p).natDegree := by
      rewrite [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
      exact positive
    (horizontal prepared nonzero positive parameter safe).right =
      Path.Components.pathImag (normalizedLeft prepared rotatedPositive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection -
      Path.Components.pathImag (normalizedRight prepared rotatedPositive parameter)
        (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection := rfl

end Purelib.Polynomial.Elimination.Axis.Separated.Prepared

end
