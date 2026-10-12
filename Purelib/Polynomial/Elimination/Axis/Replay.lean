module
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Elimination.Axis.Separated.Bezout
import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
import Purelib.Polynomial.Elimination.Separated.Scalar

import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Elimination.Separated.Bezout.Replay
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
Restore the original axis certificate from checked separated-Sylvester data.
Both the scalar polynomials and the executable Bézout callbacks consume those
data. The degree bound is read from the restored polynomials as well.
These are the existing finite constructors, with their recursive inverse
inputs supplied by exact replay; no alternate eliminant is introduced.
-/

namespace Purelib.Polynomial.Elimination.Axis.Replay

open Purelib.Polynomial.Elimination.SylvesterBezout
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

/-- Replay a vertical coordinate coprimality certificate from retained elimination data.

The saved nonzero eliminant, positive constant and clear vertical line produce the coordinate certificate using the
original normalized cofactors. -/
@[expose] def vertical (saved : Elimination.Separated.Bezout.Replay.Saved p) (nonzero : p.isZero = false) (positive : 0
  < p.natDegree)
    (x : Fraction.Rational) (clear : (Elimination.Separated.Bezout.Replay.eliminant saved).eval x ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p x)
      (Dense.Gaussian.Path.Axis.verticalPathImag p x) where
  left := Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Replay.normalizedLeft saved positive x)
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit +
    Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Replay.normalizedRight saved positive x)
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  right := Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Replay.normalizedLeft saved positive x)
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit -
    Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Replay.normalizedRight saved positive x)
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  identity := by
    rcases saved with ⟨value, same⟩
    cases same
    exact (Purelib.Polynomial.Elimination.Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero positive x
      clear).identity

/-- Replay a horizontal coordinate coprimality certificate from retained elimination data.

The quarter-turned saved eliminant and its positive constant certify the horizontal coordinate pair without repeating
elimination. -/
@[expose] def horizontal (saved : Elimination.Separated.Bezout.Replay.Saved
  (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)) (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) (y : Fraction.Rational) (clear : (Elimination.Separated.Bezout.Replay.eliminant
      saved).eval y ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.horizontalPathReal p y)
      (Dense.Gaussian.Path.Axis.horizontalPathImag p y) :=
  let rotatedPositive : 0 < (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p).natDegree := by
    rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  { left := Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Replay.normalizedLeft saved
    rotatedPositive y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection +
      Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Replay.normalizedRight saved rotatedPositive
        y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
    right := Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Replay.normalizedLeft saved
      rotatedPositive y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection -
      Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Replay.normalizedRight saved rotatedPositive
        y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
    identity := by
      rcases saved with ⟨value, same⟩
      cases same
      exact (Elimination.Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero positive y clear).identity }

/-- Read the maximum degree of the two retained axis eliminants. -/
@[expose] def degree (first : Elimination.Separated.Bezout.Replay.Saved p) (second :
  Elimination.Separated.Bezout.Replay.Saved (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)) : Nat :=
  max (Elimination.Separated.Bezout.Replay.eliminant first).natDegree (Elimination.Separated.Bezout.Replay.eliminant
    second).natDegree

/-- The degree read from retained eliminants equals the separated elimination degree. -/
theorem degree_eq (first : Elimination.Separated.Bezout.Replay.Saved p) (second :
  Elimination.Separated.Bezout.Replay.Saved (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)) :
    Elimination.Axis.Replay.degree first second = Elimination.Axis.Separated.separatedEliminationDegree p := by
  unfold Elimination.Axis.Replay.degree
  rw [Elimination.Separated.Bezout.Replay.eliminant_eq first, Elimination.Separated.Bezout.Replay.eliminant_eq second]
  rfl

/-- Assemble both axis coprimality callbacks from their retained elimination computations.

The resulting certificate keeps the original separated elimination data and supplies vertical and horizontal replay from
those exact saved values. -/
@[expose] def certificate (first : Elimination.Separated.Bezout.Replay.Saved p) (second :
  Elimination.Separated.Bezout.Replay.Saved (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p (Elimination.Axis.Replay.degree first second)
      where
  vertical := Elimination.Separated.Bezout.Replay.eliminant first
  horizontal := Elimination.Separated.Bezout.Replay.eliminant second
  vertical_nonzero := by rw [Elimination.Separated.Bezout.Replay.eliminant_eq]; exact
    Purelib.Polynomial.Elimination.Separated.Scalar.scalarEliminant_nonzero p nonzero
  horizontal_nonzero := by
    rw [Elimination.Separated.Bezout.Replay.eliminant_eq]
    exact Purelib.Polynomial.Elimination.Axis.Separated.Eliminant.horizontalEliminant_nonzero p nonzero
  vertical_degree := by
    unfold degree
    rw [Purelib.Data.Nat.Order.max_eq_natMax]
    exact Purelib.Data.Nat.Order.le_max_left _ _
  horizontal_degree := by
    unfold degree
    rw [Purelib.Data.Nat.Order.max_eq_natMax]
    exact Purelib.Data.Nat.Order.le_max_right _ _
  vertical_coprime := Elimination.Axis.Replay.vertical first nonzero positive
  horizontal_coprime := Elimination.Axis.Replay.horizontal second nonzero positive

/-- Structural equality includes the executable coprimality callbacks. -/
theorem certificate_eq (first : Elimination.Separated.Bezout.Replay.Saved p) (second :
  Elimination.Separated.Bezout.Replay.Saved (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    (Elimination.Axis.Replay.degree_eq first second) ▸ Elimination.Axis.Replay.certificate first second nonzero positive
      =
      Elimination.Axis.Separated.separatedAxisEliminationCertificate p nonzero positive := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  rfl
end Purelib.Polynomial.Elimination.Axis.Replay

end
