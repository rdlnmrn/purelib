module
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
public import Purelib.Polynomial.Elimination.Axis.Separated.Bezout
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
  max (Elimination.Separated.Scalar.scalarEliminant p).natDegree
    (Elimination.Axis.Separated.Eliminant.horizontalEliminant p).natDegree

/-- Closed constructive axis-elimination data from the two fraction-free
separated Sylvester inverses.

The original nonzero positive-degree source supplies both nonzero
coordinate eliminants. Their same finite cofactors certify coprimality
whenever the corresponding scalar value is nonzero. -/
@[expose] def separatedAxisEliminationCertificate (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      (Elimination.Axis.Separated.separatedEliminationDegree p) where
  vertical := Elimination.Separated.Scalar.scalarEliminant p
  horizontal := Elimination.Axis.Separated.Eliminant.horizontalEliminant p
  vertical_nonzero :=
    Elimination.Separated.Scalar.scalarEliminant_nonzero p nonzero
  horizontal_nonzero :=
    Elimination.Axis.Separated.Eliminant.horizontalEliminant_nonzero p nonzero
  vertical_degree := by
    change (Elimination.Separated.Scalar.scalarEliminant p).natDegree ≤
      max (Elimination.Separated.Scalar.scalarEliminant p).natDegree
        (Elimination.Axis.Separated.Eliminant.horizontalEliminant p).natDegree
    rw [Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_left _ _
  horizontal_degree := by
    change (Elimination.Axis.Separated.Eliminant.horizontalEliminant p).natDegree ≤
      max (Elimination.Separated.Scalar.scalarEliminant p).natDegree
        (Elimination.Axis.Separated.Eliminant.horizontalEliminant p).natDegree
    rw [Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_right _ _
  vertical_coprime := by
    intro x eliminantNonzero
    simpa only [Dense.Gaussian.Path.Axis.verticalPathReal, Dense.Gaussian.Path.Axis.verticalPathImag] using
      Elimination.Axis.Separated.Bezout.verticalCoprimeCertificate p nonzero
        degreePositive x eliminantNonzero
  horizontal_coprime := by
    intro y eliminantNonzero
    simpa only [Dense.Gaussian.Path.Axis.horizontalPathReal, Dense.Gaussian.Path.Axis.horizontalPathImag] using
      Elimination.Axis.Separated.Bezout.horizontalCoprimeCertificate p nonzero
        degreePositive y eliminantNonzero

end Purelib.Polynomial.Elimination.Axis.Separated

end
