module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.QuadraticTarget.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RationalFunctions.Approximation.Height.Basic
public import Purelib.RationalFunctions.Approximation.Height.Budget
public import Purelib.RationalFunctions.Approximation.Height.Build
import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic

section
@[expose] public section

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Target

open Purelib.Approximation
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Construct a protected quotient approximation using the quadratic request for the displayed target.

Retain the source degree bound, squarefree and elimination certificates, and the context's exact quotient coefficient.
The request generator supplies a positive epsilon. -/
def approximateTarget
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box} {degreeBound : Nat}
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source
      degreeBound)
    (target : Rat.Fraction.Rational) :
    Approximation.Height.Basic.Output context degreeAtLeastTwo squarefree elimination
      (Rational.QuadraticTarget.Basic.targetEpsilon
        (Approximation.Height.Budget.targetCoefficient context) target) :=
  Approximation.Height.Build.approximate context degreeAtLeastTwo squarefree elimination
    (Rational.QuadraticTarget.Basic.targetEpsilon_pos _ target)

/-- The denominator-controlled approximation has quotient residual at most a positive target.

The retained quotient estimate combines with the exact quadratic-target coefficient bound. -/
theorem approximateTarget_quotientResidual_le
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box} {degreeBound : Nat}
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source
      degreeBound)
    {target : Rat.Fraction.Rational} (targetPositive : 0 < target) :
    Residual.Basic.quotientResidualSq source opposite
        (approximateTarget context degreeAtLeastTwo squarefree elimination
          target).polynomial.fraction.value ≤ target := by
  have coefficientBound :=
    Rational.QuadraticTarget.Basic.coefficient_mul_targetEpsilon_sq_le
      (Approximation.Height.Budget.targetCoefficient_pos context) targetPositive
  have outputBound :=
    (approximateTarget context degreeAtLeastTwo squarefree elimination
      target).quotientResidual_le
  rw [Approximation.Height.Budget.targetCoefficient_mul_epsilon_sq] at outputBound
  exact outputBound.trans coefficientBound

end Purelib.RationalFunctions.Approximation.Height.Target

end
