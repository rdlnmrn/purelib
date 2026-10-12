module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
public import Purelib.RootIsolation.Approximation.Denominator
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box

section
@[expose] public section

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Basic

set_option genInjectivity false in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- A denominator-controlled source approximation with its protected quotient-residual bound.

The polynomial result is indexed by the context's protected state, the supplied squarefree and elimination certificates,
and epsilon. Its exact fraction value satisfies the retained quotient estimate using the opposite-polynomial margin. -/
structure Output
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box} {degreeBound : Nat}
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source
      degreeBound)
    (epsilon : Rat.Fraction.Rational) where
  /-- The retained denominator-controlled polynomial approximation at the protected source state. -/ polynomial :
    Approximation.Denominator.Output degreeAtLeastTwo squarefree
    elimination context.protectedState.raw epsilon
  /-- The retained fraction's quotient residual is bounded by the displayed Lipschitz estimate divided by the opposite
    margin. -/ quotientResidual_le :
    Residual.Basic.quotientResidualSq source opposite
        polynomial.fraction.value ≤
      (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2) /
        context.oppositeMargin

constructive_injectivity Output

end Purelib.RationalFunctions.Approximation.Height.Basic

end
