module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RationalFunctions.Approximation.Height.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.RootIsolation.Approximation.Denominator
import Purelib.RootIsolation.Newton.Band.State
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.RationalFunctions.Residual.Local.Bounds
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Build

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Construct a denominator-controlled sample with a protected quotient-residual estimate.

The source has degree at least two, executable squarefreeness and elimination certificates, and a positive epsilon
request. The polynomial approximation is retained exactly, and its refined box supplies the quotient bound using the
context's opposite margin. -/
def approximate
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box} {degreeBound : Nat}
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source
      degreeBound)
    {epsilon : Rat.Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    Approximation.Height.Basic.Output context degreeAtLeastTwo squarefree elimination epsilon := by
  let polynomial := Approximation.Denominator.approximate degreeAtLeastTwo
    squarefree elimination context.protectedState.raw epsilonPositive
  let state := Newton.Band.State.stateOfOutput polynomial.extracted
  have refinesProtected : state.box.Refines context.protectedState.box := by
    exact (Geometry.Rational.Box.Refinement.StrictInterior.refines polynomial.extracted.strictCurrent)
  have quotientBound := (Residual.Local.Basic.LocalQuotientContext.quotientResidualSq_le_diagonal context)
    refinesProtected polynomial.strictlyInside.contains
  have numeratorBound :
      4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq ≤
        2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2 := by
    calc
      4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq ≤
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient *
            ((1 / 2 : Rat.Fraction.Rational) * epsilon ^ 2) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          polynomial.extracted.diagonalSq_le_half
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos source ambient).le)
      _ = 2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2 := by
        have fourHalf : (4 : Rat.Fraction.Rational) * (1 / 2) = 2 := by decide
        calc
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient *
              ((1 / 2 : Rat.Fraction.Rational) * epsilon ^ 2) =
              ((4 : Rat.Fraction.Rational) * (1 / 2)) *
                Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2 := by ring1
          _ = 2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2 := by
            rw [fourHalf]
  have dividedBound :
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq) /
          context.oppositeMargin ≤
        (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2) /
          context.oppositeMargin := by
    change
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq) *
          context.oppositeMargin⁻¹ ≤
        (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2) *
          context.oppositeMargin⁻¹
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      numeratorBound
      (Rat.Fraction.Order.Field.inv_pos_direct
        context.oppositeMargin_pos).le
  exact
    { polynomial := polynomial
      quotientResidual_le := quotientBound.trans dividedBound }
end Purelib.RationalFunctions.Approximation.Height.Build

end
