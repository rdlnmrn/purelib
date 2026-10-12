module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Diagonal and paired residual thresholds

The retained derivative margin and finite Taylor bound determine the
original uniqueness and paired residual budgets with positivity certificates.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness

/-- Compute the squared-diagonal threshold from the retained derivative margin.

The margin is divided by eight times the original ambient Taylor-remainder
bound. The retained derivative-separation certificate supplies its positivity. -/
@[expose] public def separatedUniquenessDiagonalThreshold
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (ambient : Box)
    (separation : Basic.Certificate p ambient) :
      Fraction.Rational :=
  separation.margin / (8 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient)

/-- The derivative-separation diagonal threshold is positive.

A positive retained derivative margin is divided by a positive Taylor-remainder budget. -/
public theorem separatedUniquenessDiagonalThreshold_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (ambient : Box)
    (separation : Basic.Certificate p ambient) :
    0 < Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold ambient separation := by
  exact Fraction.Order.Field.div_pos_direct separation.margin_pos
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide))
      (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient))

/-- Squarefree specialization retained for the finite-packing interface. -/
@[expose] public def uniquenessDiagonalThreshold
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) : Fraction.Rational :=
  Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold
    ambient (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)

/-- The diagonal threshold computed from a squarefree certificate is positive. -/
public theorem uniquenessDiagonalThreshold_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) : 0 < Dense.Gaussian.Derivative.Separation.Uniqueness.uniquenessDiagonalThreshold
      squarefree ambient := by
  exact Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold_pos
    ambient (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)

/-- Compute the paired residual budget from a retained separation gap.

The minimum keeps both the original residual threshold and one thirty-second
of the derivative margin times the gap square. Positivity requires a positive gap. -/
@[expose] public def separatedPairResidualThreshold
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (ambient : Box)
    (separation : Basic.Certificate p ambient)
    (gap : Fraction.Rational) : Fraction.Rational :=
  min separation.threshold
    ((1 / 32 : Fraction.Rational) * (separation.margin * gap ^ 2))

/-- A positive gap gives a positive paired residual threshold.

Both the retained threshold and the margin times the squared gap are positive. -/
public theorem separatedPairResidualThreshold_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (ambient : Box)
    (separation : Basic.Certificate p ambient)
    {gap : Fraction.Rational} (gapPositive : 0 < gap) :
    0 < Dense.Gaussian.Derivative.Separation.Uniqueness.separatedPairResidualThreshold ambient separation gap := by
  exact Fraction.Order.Basic.lt_min separation.threshold_pos
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by decide))
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)))
      (Fraction.Order.Arithmetic.mul_pos_direct separation.margin_pos
        (Fraction.Order.Arithmetic.pow_pos_direct gapPositive 2)))

/-- Squarefree specialization of the separated residual budget. -/
@[expose] public def pairResidualThreshold
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) (gap : Fraction.Rational) : Fraction.Rational :=
  Dense.Gaussian.Derivative.Separation.Uniqueness.separatedPairResidualThreshold
    ambient (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient) gap

/-- The squarefree paired residual threshold is positive for a positive gap. -/
public theorem pairResidualThreshold_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) {gap : Fraction.Rational} (gapPositive : 0 < gap) :
    0 < Dense.Gaussian.Derivative.Separation.Uniqueness.pairResidualThreshold squarefree ambient gap := by
  exact Dense.Gaussian.Derivative.Separation.Uniqueness.separatedPairResidualThreshold_pos
    ambient (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)
      gapPositive

end Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
