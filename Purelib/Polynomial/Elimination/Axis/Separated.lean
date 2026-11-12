module
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
public import Purelib.Polynomial.Elimination.Axis.Separated.Replay
import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
import Purelib.Polynomial.Elimination.Separated.Scalar
import Mathlib.Data.Nat.Basic
-- The existing public Certificate → Rational.Bezout.Basic → Fraction.Field path exposes Nat.Order.
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bezout.Basic

/-!
# Separated axis elimination certificates

The vertical and horizontal eliminants retain their common degree bound
and finite rational Bezout certificates. Every field concerns the same
source Gaussian polynomial and its original coordinate line.
-/

public section

namespace Purelib.Polynomial.Elimination.Axis.Separated

open Purelib
open Purelib.Polynomial

/-- The actual finite degree bound of the two separated-Sylvester
eliminants.

The maximum retains the two actual natural degrees as its arguments and
bounds both coordinate eliminants. -/
@[expose] def separatedEliminationDegree (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : Nat :=
  max (Separated.Scalar.scalarEliminant p).natDegree
    (Eliminant.horizontalEliminant p).natDegree

/-- Assemble original axis callbacks from retained scalar polynomials with their exact canonical readbacks.

Both actual polynomials and their maximum degree are consumed directly. Each
nonzero-evaluation hypothesis is transported to the original checked-column
callback, retaining its canonical cofactors and total fallback procedure.
-/
@[expose] def certificateFromPolynomials
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (vertical horizontal : Dense.Rational.Basic.CoordinatePolynomial)
    (verticalSame : vertical = Separated.Scalar.scalarEliminant p)
    (horizontalSame : horizontal = Eliminant.horizontalEliminant p) :
    Certificate.AxisSafeCuts.AxisEliminationCertificate p
      (max vertical.natDegree horizontal.natDegree) where
  vertical := vertical
  horizontal := horizontal
  vertical_nonzero := by
    rewrite [verticalSame]
    exact Separated.Scalar.scalarEliminant_nonzero p nonzero
  horizontal_nonzero := by
    rewrite [horizontalSame]
    exact Eliminant.horizontalEliminant_nonzero p nonzero
  vertical_degree := by
    rewrite [Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_left _ _
  horizontal_degree := by
    rewrite [Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_right _ _
  vertical_coprime := fun coordinate safe =>
    (Replay.computeVertical p nonzero degreePositive coordinate
      (fun zero => safe ((congrArg (fun polynomial => polynomial.eval coordinate) verticalSame).trans zero))).val
  horizontal_coprime := fun coordinate safe =>
    (Replay.computeHorizontal p nonzero degreePositive coordinate
      (fun zero => safe ((congrArg (fun polynomial => polynomial.eval coordinate) horizontalSame).trans zero))).val

/-- Closed constructive axis-elimination data from the two fraction-free separated Sylvester inverses.

The original nonzero positive-degree source supplies both nonzero coordinate
eliminants. Their retained scalar polynomials and the original checked-column
callbacks certify the same coordinate lines.
-/
@[expose] def separatedAxisEliminationCertificate
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree) :
    Certificate.AxisSafeCuts.AxisEliminationCertificate p (separatedEliminationDegree p) :=
  certificateFromPolynomials p nonzero degreePositive
    (Separated.Scalar.scalarEliminant p) (Eliminant.horizontalEliminant p) rfl rfl

/-- Exact scalar readbacks identify the retained maximum degree with the canonical search bound. -/
theorem certificateFromPolynomials_degree
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (vertical horizontal : Dense.Rational.Basic.CoordinatePolynomial)
    (verticalSame : vertical = Separated.Scalar.scalarEliminant p)
    (horizontalSame : horizontal = Eliminant.horizontalEliminant p) :
    max vertical.natDegree horizontal.natDegree = separatedEliminationDegree p :=
  congrArg₂ (fun left right : Dense.Rational.Basic.CoordinatePolynomial =>
    max left.natDegree right.natDegree) verticalSame horizontalSame

/-- The retained-polynomial constructor transports to the complete canonical certificate.

The original scalar identities identify the maximum degree and both callback
domains. Equality elimination preserves the same executable callback bodies.
-/
theorem certificateFromPolynomials_eq
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (vertical horizontal : Dense.Rational.Basic.CoordinatePolynomial)
    (verticalSame : vertical = Separated.Scalar.scalarEliminant p)
    (horizontalSame : horizontal = Eliminant.horizontalEliminant p) :
    (certificateFromPolynomials_degree p vertical horizontal verticalSame horizontalSame) ▸
        certificateFromPolynomials p nonzero positive vertical horizontal verticalSame horizontalSame =
      separatedAxisEliminationCertificate p nonzero positive := by
  cases verticalSame
  cases horizontalSame
  rfl

end Purelib.Polynomial.Elimination.Axis.Separated

end
