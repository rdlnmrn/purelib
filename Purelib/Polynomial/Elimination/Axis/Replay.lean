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
import Purelib.Polynomial.Elimination.Axis.Separated.Replay
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

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
Restore scalar axis eliminants from checked separated-Sylvester data while
retaining the canonical track-refinement callbacks. The same saved inverse
also supplies exact per-request Bézout certificates for clearance loaders.
Whole certificate equality and pointwise cached-cofactor equality are proved
separately; neither requires equality of independently implemented functions.
-/

namespace Purelib.Polynomial.Elimination.Axis.Replay

open Purelib.Polynomial.Elimination.SylvesterBezout
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {p : Basic.CanonicalCoefficients.CoefficientPolynomial}

/-- Replay a vertical coordinate coprimality certificate from retained elimination data.

The saved nonzero eliminant, positive constant and clear vertical line produce the coordinate certificate using the
original normalized cofactors. -/
@[expose] def vertical (saved : Separated.Bezout.Replay.Saved p) (nonzero : p.isZero = false) (positive : 0
  < p.natDegree)
    (x : Fraction.Rational) (clear : (Separated.Bezout.Replay.eliminant saved).eval x ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Path.Axis.verticalPathReal p x)
      (Path.Axis.verticalPathImag p x) where
  left := Path.Components.pathReal (Separated.Bezout.Replay.normalizedLeft saved positive x)
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit +
    Path.Components.pathReal (Separated.Bezout.Replay.normalizedRight saved positive x)
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  right := Path.Components.pathImag (Separated.Bezout.Replay.normalizedLeft saved positive x)
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit -
    Path.Components.pathImag (Separated.Bezout.Replay.normalizedRight saved positive x)
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
  identity := by
    have originalClear : (Separated.Scalar.scalarEliminant p).eval x ≠ 0 := by
      rewrite [← Separated.Bezout.Replay.eliminant_eq saved]
      exact clear
    rcases saved with ⟨value, same⟩
    cases same
    exact (Separated.Bezout.verticalCoprimeCertificate p nonzero positive x
      originalClear).identity

/-- Replay a horizontal coordinate coprimality certificate from retained elimination data.

The quarter-turned saved eliminant and its positive constant certify the horizontal coordinate pair without repeating
elimination. -/
@[expose] def horizontal (saved : Separated.Bezout.Replay.Saved
  (Substitution.QuarterTurn.quarterTurn p)) (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) (y : Fraction.Rational) (clear : (Separated.Bezout.Replay.eliminant
      saved).eval y ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Path.Axis.horizontalPathReal p y)
      (Path.Axis.horizontalPathImag p y) :=
  let rotatedPositive : 0 < (Substitution.QuarterTurn.quarterTurn p).natDegree := by
    rw [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  { left := Path.Components.pathReal (Separated.Bezout.Replay.normalizedLeft saved
    rotatedPositive y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection +
      Path.Components.pathReal (Separated.Bezout.Replay.normalizedRight saved rotatedPositive
        y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
    right := Path.Components.pathImag (Separated.Bezout.Replay.normalizedLeft saved
      rotatedPositive y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection -
      Path.Components.pathImag (Separated.Bezout.Replay.normalizedRight saved rotatedPositive
        y) (Gaussian.Cast.Winding.verticalBase y) Affine.Axis.negativeVerticalDirection
    identity := by
      have originalClear : (Separated.Eliminant.horizontalEliminant p).eval y ≠ 0 := by
        unfold Separated.Eliminant.horizontalEliminant
        rewrite [← Separated.Bezout.Replay.eliminant_eq saved]
        exact clear
      rcases saved with ⟨value, same⟩
      cases same
      exact (Separated.Bezout.horizontalCoprimeCertificate p nonzero positive y originalClear).identity }

/-- Read the maximum degree of the two retained axis eliminants. -/
@[expose] def degree (first : Separated.Bezout.Replay.Saved p) (second :
  Separated.Bezout.Replay.Saved (Substitution.QuarterTurn.quarterTurn p)) : Nat :=
  max (Separated.Bezout.Replay.eliminant first).natDegree (Separated.Bezout.Replay.eliminant
    second).natDegree

/-- The degree read from retained eliminants equals the separated elimination degree. -/
theorem degree_eq (first : Separated.Bezout.Replay.Saved p) (second :
  Separated.Bezout.Replay.Saved (Substitution.QuarterTurn.quarterTurn p)) :
    degree first second = Separated.separatedEliminationDegree p := by
  unfold degree
  rw [Separated.Bezout.Replay.eliminant_eq first, Separated.Bezout.Replay.eliminant_eq second]
  rfl

/-- Assemble the canonical axis callbacks while consuming retained original scalar polynomials and degree.

The scalar readings consume the saved inverse data. Both callbacks use the
original checked-column procedure and fallback, sharing the canonical
constructor so its complete refinement functions remain identical. The
separate `vertical` and `horizontal` operations consume saved inverse cofactors.
-/
@[expose] def certificate (first : Separated.Bezout.Replay.Saved p) (second :
  Separated.Bezout.Replay.Saved (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    Certificate.AxisSafeCuts.AxisEliminationCertificate p (degree first second) :=
  Separated.certificateFromPolynomials p nonzero positive
    (Separated.Bezout.Replay.eliminant first) (Separated.Bezout.Replay.eliminant second)
    (Separated.Bezout.Replay.eliminant_eq first) (Separated.Bezout.Replay.eliminant_eq second)

/-- Structural equality retains the original scalar polynomials and executable coprimality callbacks.

The shared canonical constructor fixes the complete callback functions.
The retained inverse scalar identities transport their coordinate polynomials
and degree index before comparing the complete original certificate.
-/
theorem certificate_eq (first : Separated.Bezout.Replay.Saved p) (second :
    Separated.Bezout.Replay.Saved (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    (degree_eq first second) ▸ certificate first second nonzero positive =
      Separated.separatedAxisEliminationCertificate p nonzero positive := by
  exact Separated.certificateFromPolynomials_eq p nonzero positive
    (Separated.Bezout.Replay.eliminant first) (Separated.Bezout.Replay.eliminant second)
    (Separated.Bezout.Replay.eliminant_eq first) (Separated.Bezout.Replay.eliminant_eq second)

/-- A replayed vertical certificate has the complete original cofactors at the same parameter.

Only the scalar nonzero hypothesis is transported through the retained
eliminant equality. The actual original normalized inverse data supplies
both executable cofactors and their pointwise identity.
-/
theorem vertical_eq (saved : Separated.Bezout.Replay.Saved p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational)
    (clear : (Separated.Bezout.Replay.eliminant saved).eval parameter ≠ 0) :
    vertical saved nonzero positive parameter clear =
      Separated.Bezout.verticalCoprimeCertificate p nonzero positive parameter
        (fun zero => clear ((congrArg (fun polynomial => polynomial.eval parameter)
          (Separated.Bezout.Replay.eliminant_eq saved)).trans zero)) := by
  rcases saved with ⟨value, same⟩
  cases same
  rfl

/-- A replayed horizontal certificate has the complete original cofactors at the same parameter.

The quarter-turned original scalar reading transports the nonzero condition;
the actual saved inverse data retains the original horizontal cofactors.
-/
theorem horizontal_eq (saved : Separated.Bezout.Replay.Saved (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational)
    (clear : (Separated.Bezout.Replay.eliminant saved).eval parameter ≠ 0) :
    horizontal saved nonzero positive parameter clear =
      Separated.Bezout.horizontalCoprimeCertificate p nonzero positive parameter
        (fun zero => clear ((congrArg (fun polynomial => polynomial.eval parameter)
          (Separated.Bezout.Replay.eliminant_eq saved)).trans zero)) := by
  rcases saved with ⟨value, same⟩
  cases same
  rfl

end Purelib.Polynomial.Elimination.Axis.Replay

end
