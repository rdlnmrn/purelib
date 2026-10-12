module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Elimination.Axis.Separated.Bezout
import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
public import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Elimination.Separated.Bezout.Normalized

open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
/-!
Checked finite witnesses for the original separated-Sylvester clearances.
An untrusted column solves the evaluated matrix equation. The original scaled
inverse proves uniqueness, so the saved column supplies the original normalized
cofactors, rather than merely some valid Bezout coefficients. Equality of the
resulting rational polynomials uses the existing explicit finite-grid theorem.
-/

@[expose] public section

namespace Purelib.Polynomial.Elimination

/-- Replay the original vertical coprimality certificate from a checked separated-system column.

The returned subtype certifies equality to the original constructor, including its exact cofactors, using the supplied
nonzero eliminant value. -/
def Separated.Replay.Column.vertical {p positive parameter} (column :
  Elimination.Separated.Replay.Column p positive parameter)
    (nonzero : p.isZero = false) (safe : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) :
    { value : CoprimeCertificate
        (Dense.Gaussian.Path.Axis.verticalPathReal p parameter) (Dense.Gaussian.Path.Axis.verticalPathImag p parameter)
          //
      value = Elimination.Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero positive parameter safe } :=
  let left := column.pathLeft (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit
  let right := column.pathRight (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit
  have leftEq : left = Elimination.Axis.Separated.Bezout.verticalBezoutLeft p positive parameter := column.pathLeft_eq
    safe _ _
  have rightEq : right = Elimination.Axis.Separated.Bezout.verticalBezoutRight p positive parameter :=
    column.pathRight_eq safe _ _
  let result : CoprimeCertificate
      (Dense.Gaussian.Path.Axis.verticalPathReal p parameter) (Dense.Gaussian.Path.Axis.verticalPathImag p parameter) :=
    { left := left
      right := right
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact (Elimination.Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero positive parameter safe).identity
          point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

/-- Replay the original horizontal coprimality certificate from a checked quarter-turn column.

The returned subtype retains equality with the original certificate at the same parameter and degree witness; its two
cofactors are read from the supplied column. -/
def Axis.Separated.Replay.horizontal (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : p.isZero = false) (positive : 0 <
    p.natDegree)
    (parameter : Fraction.Rational) (safe : (Elimination.Axis.Separated.Eliminant.horizontalEliminant p).eval parameter
      ≠ 0)
    (column : Elimination.Separated.Replay.Column (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)
      (by
        rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]; exact positive) parameter) :
    { value : CoprimeCertificate
        (Dense.Gaussian.Path.Axis.horizontalPathReal p parameter) (Dense.Gaussian.Path.Axis.horizontalPathImag p
          parameter) //
      value = Elimination.Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero positive parameter safe } :=
  let left := column.pathLeft (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection
  let right := column.pathRight (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection
  have leftEq : left = Elimination.Axis.Separated.Bezout.horizontalBezoutLeft p nonzero positive parameter :=
    column.pathLeft_eq safe _ _
  have rightEq : right = Elimination.Axis.Separated.Bezout.horizontalBezoutRight p nonzero positive parameter :=
    column.pathRight_eq safe _ _
  let result : CoprimeCertificate
      (Dense.Gaussian.Path.Axis.horizontalPathReal p parameter) (Dense.Gaussian.Path.Axis.horizontalPathImag p
        parameter) :=
    { left := left
      right := right
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact (Elimination.Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero positive parameter
          safe).identity point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

end Purelib.Polynomial.Elimination

end
