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
-- Public prepared replay results identify these original full certificates.
public import Purelib.Polynomial.Elimination.Axis.Separated.Prepared
import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
public import Purelib.Polynomial.Elimination.Separated.Replay
public import Purelib.Polynomial.Elimination.Separated.Replay.Computation
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

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Substitution
open Purelib.Polynomial.Elimination.Separated.Replay (Invalid check propose)
open Purelib.Polynomial.Elimination.Separated.Replay.Computation (compute)
open Purelib.Polynomial.Elimination.Separated.Preparation renaming Prepared -> SylvesterPreparation
open Purelib.Polynomial.Dense.Gaussian.Path

open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian

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
  Separated.Replay.Column p positive parameter)
    (nonzero : p.isZero = false) (safe : (Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) :
    { value : CoprimeCertificate
        (Axis.verticalPathReal p parameter) (Axis.verticalPathImag p parameter)
          //
      value = Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero positive parameter safe } :=
  let coordinates := column.pathCofactors (Gaussian.Cast.Winding.verticalBase parameter)
    Gaussian.Constants.imaginaryUnit
  let left := coordinates.1
  let right := coordinates.2
  have leftEq : left = Axis.Separated.Bezout.verticalBezoutLeft p positive parameter :=
    (column.pathCofactors_left _ _).trans (column.pathLeft_eq safe _ _)
  have rightEq : right = Axis.Separated.Bezout.verticalBezoutRight p positive parameter :=
    (column.pathCofactors_right _ _).trans (column.pathRight_eq safe _ _)
  let result : CoprimeCertificate
      (Axis.verticalPathReal p parameter) (Axis.verticalPathImag p parameter) :=
    { left := left
      right := right
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact (Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero positive parameter safe).identity
          point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

/-- Replay the original horizontal coprimality certificate from a checked quarter-turn column.

The returned subtype retains equality with the original certificate at the same parameter and degree witness; its two
cofactors are read from the supplied column. -/
def Axis.Separated.Replay.horizontal (p :
  CoefficientPolynomial) (nonzero : p.isZero = false) (positive : 0 <
    p.natDegree)
    (parameter : Fraction.Rational) (safe : (Axis.Separated.Eliminant.horizontalEliminant p).eval parameter
      ≠ 0)
    (column : Separated.Replay.Column (QuarterTurn.quarterTurn p)
      (by
        rw [QuarterTurn.quarterTurn_natDegree p nonzero]; exact positive) parameter) :
    { value : CoprimeCertificate
        (Axis.horizontalPathReal p parameter) (Axis.horizontalPathImag p
          parameter) //
      value = Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero positive parameter safe } :=
  let coordinates := column.pathCofactors (Gaussian.Cast.Winding.verticalBase parameter)
    Affine.Axis.negativeVerticalDirection
  let left := coordinates.1
  let right := coordinates.2
  have leftEq : left = Axis.Separated.Bezout.horizontalBezoutLeft p nonzero positive parameter :=
    (column.pathCofactors_left _ _).trans (column.pathLeft_eq safe _ _)
  have rightEq : right = Axis.Separated.Bezout.horizontalBezoutRight p nonzero positive parameter :=
    (column.pathCofactors_right _ _).trans (column.pathRight_eq safe _ _)
  let result : CoprimeCertificate
      (Axis.horizontalPathReal p parameter) (Axis.horizontalPathImag p
        parameter) :=
    { left := left
      right := right
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact (Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero positive parameter
          safe).identity point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

namespace Separated.Replay.Column

open Axis.Separated

/-- Restore the complete retained-preparation vertical certificate from one checked unit column.

The original prepared eliminant supplies the nonzero scalar condition. Both
cofactor tables come from the supplied column, and the returned equality
retains the original prepared constructor and its complete proof field. -/
def verticalFromPrepared {p positive parameter} (column : Column p positive parameter)
    (prepared : SylvesterPreparation p) (nonzero : p.isZero = false)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    { value : CoprimeCertificate (Path.Axis.verticalPathReal p parameter) (Path.Axis.verticalPathImag p parameter) //
      value = Prepared.vertical prepared nonzero positive parameter safe } :=
  let coordinates := column.pathCofactors (Gaussian.Cast.Winding.verticalBase parameter)
    Gaussian.Constants.imaginaryUnit
  let original := Prepared.vertical prepared nonzero positive parameter safe
  have same := column.pathCofactors_eq_prepared prepared (prepared.scalar_ne_zero parameter safe)
    (Gaussian.Cast.Winding.verticalBase parameter) Gaussian.Constants.imaginaryUnit
  have leftEq : coordinates.1 = original.left :=
    (congrArg Prod.fst same).trans (Prepared.vertical_left prepared nonzero positive parameter safe).symm
  have rightEq : coordinates.2 = original.right :=
    (congrArg Prod.snd same).trans (Prepared.vertical_right prepared nonzero positive parameter safe).symm
  let result : CoprimeCertificate (Path.Axis.verticalPathReal p parameter) (Path.Axis.verticalPathImag p parameter) :=
    { left := coordinates.1
      right := coordinates.2
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact original.identity point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

end Separated.Replay.Column

namespace Axis.Separated.Replay

/-- Restore the complete retained-preparation horizontal certificate from its checked quarter-turn column.

The actual original polynomial, its quarter-turned preparation and their
degree witnesses remain attached. Both returned cofactor tables are the
original horizontal constructor's tables, with its complete certificate equality. -/
def horizontalFromPrepared (p : CoefficientPolynomial)
    (prepared : SylvesterPreparation (QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0)
    (column : Elimination.Separated.Replay.Column (QuarterTurn.quarterTurn p)
      (by rewrite [QuarterTurn.quarterTurn_natDegree p nonzero]; exact positive) parameter) :
    { value : CoprimeCertificate
        (Path.Axis.horizontalPathReal p parameter) (Path.Axis.horizontalPathImag p parameter) //
      value = Prepared.horizontal prepared nonzero positive parameter safe } :=
  let coordinates := column.pathCofactors (Gaussian.Cast.Winding.verticalBase parameter)
    Affine.Axis.negativeVerticalDirection
  let original := Prepared.horizontal prepared nonzero positive parameter safe
  have same := column.pathCofactors_eq_prepared prepared (prepared.scalar_ne_zero parameter safe)
    (Gaussian.Cast.Winding.verticalBase parameter) Affine.Axis.negativeVerticalDirection
  have leftEq : coordinates.1 = original.left :=
    (congrArg Prod.fst same).trans (Prepared.horizontal_left prepared nonzero positive parameter safe).symm
  have rightEq : coordinates.2 = original.right :=
    (congrArg Prod.snd same).trans (Prepared.horizontal_right prepared nonzero positive parameter safe).symm
  let result : CoprimeCertificate
      (Path.Axis.horizontalPathReal p parameter) (Path.Axis.horizontalPathImag p parameter) :=
    { left := coordinates.1
      right := coordinates.2
      identity := by
        intro point
        rw [leftEq, rightEq]
        exact original.identity point }
  ⟨result, Dense.Rational.Bezout.Basic.coprime_eq _ _ leftEq rightEq⟩

end Axis.Separated.Replay

end Purelib.Polynomial.Elimination

namespace Purelib.Polynomial.Elimination.Axis.Separated.Replay

open Purelib.LinearAlgebra.Matrix.Inverse.Scaled

/-- An exact original vertical-line certificate retained through checked separated-column reconstruction. -/
abbrev VerticalCertificate (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) :=
  { value : CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p parameter)
      (Dense.Gaussian.Path.Axis.verticalPathImag p parameter) //
    value = Bezout.verticalCoprimeCertificate p nonzero positive parameter safe }

/-- An exact original horizontal-line certificate retained through checked quarter-turn column reconstruction. -/
abbrev HorizontalCertificate (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Eliminant.horizontalEliminant p).eval parameter ≠ 0) :=
  { value : CoprimeCertificate (Dense.Gaussian.Path.Axis.horizontalPathReal p parameter)
      (Dense.Gaussian.Path.Axis.horizontalPathImag p parameter) //
    value = Bezout.horizontalCoprimeCertificate p nonzero positive parameter safe }

/-- Check a displayed vertical unit column and retain the exact original certificate or actual failed row equation.

The same supplied vector and computed matrix-vector product remain in an
invalid result. Success reconstructs the original complete cofactors using
their unit-column uniqueness certificate.
-/
def verticalAttempt (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0)
    (values : GaussianColumn.Vector
      Gaussian.Basic.Canonical (p.natDegree + p.natDegree)) :
    Except (Invalid p positive parameter values)
      (VerticalCertificate p nonzero positive parameter safe) :=
  match check p positive parameter values with
  | .ok column => .ok (column.vertical nonzero safe)
  | .error failure => .error failure

/-- Use a checked vertical-column proposal, retaining the exact original constructor as a total fallback. -/
def fromVerticalProposal (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0)
    (values : GaussianColumn.Vector
      Gaussian.Basic.Canonical (p.natDegree + p.natDegree)) :
    VerticalCertificate p nonzero positive parameter safe :=
  match verticalAttempt p nonzero positive parameter safe values with
  | .ok certificate => certificate
  | .error _ => ⟨Bezout.verticalCoprimeCertificate p nonzero positive parameter safe, rfl⟩

/-- Reuse a checked direct vertical column or the original general proposal and exact fallback. -/
def computeVertical (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) :
    VerticalCertificate p nonzero positive parameter safe :=
  match (compute p positive parameter).column? with
  | some column => column.vertical nonzero safe
  | none => fromVerticalProposal p nonzero positive parameter safe
      (propose p positive parameter)

/-- Use a checked quarter-turn column proposal, retaining the exact original horizontal constructor as fallback. -/
def fromHorizontalProposal (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Eliminant.horizontalEliminant p).eval parameter ≠ 0)
    (values : GaussianColumn.Vector Gaussian.Basic.Canonical
      ((QuarterTurn.quarterTurn p).natDegree +
        (QuarterTurn.quarterTurn p).natDegree)) :
    HorizontalCertificate p nonzero positive parameter safe :=
  let rotated := QuarterTurn.quarterTurn p
  have rotatedPositive : 0 < rotated.natDegree := by
    rw [QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  match check rotated rotatedPositive parameter values with
  | .ok column => horizontal p nonzero positive parameter safe column
  | .error _ => ⟨Bezout.horizontalCoprimeCertificate p nonzero positive parameter safe, rfl⟩

/-- Reuse a checked direct quarter-turn column while preserving every original horizontal cofactor. -/
def computeHorizontal (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Fraction.Rational)
    (safe : (Eliminant.horizontalEliminant p).eval parameter ≠ 0) :
    HorizontalCertificate p nonzero positive parameter safe :=
  let rotated := QuarterTurn.quarterTurn p
  have rotatedPositive : 0 < rotated.natDegree := by
    rw [QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  match (compute rotated rotatedPositive parameter).column? with
  | some column => horizontal p nonzero positive parameter safe column
  | none => fromHorizontalProposal p nonzero positive parameter safe
      (propose rotated rotatedPositive parameter)

end Purelib.Polynomial.Elimination.Axis.Separated.Replay

end
