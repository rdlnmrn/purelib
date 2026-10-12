module
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Residual.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Residual.Local.Basic (LocalQuotientContext)

section
@[expose] public section

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace Purelib.RationalFunctions.Approximation.Height.Budget

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Compute the quadratic quotient-residual coefficient from the source Lipschitz bound and opposite margin.

The numerator is twice the source's ambient-box Lipschitz bound. Dividing by the context's protected positive
opposite-polynomial margin gives the coefficient multiplying epsilon squared. -/
def targetCoefficient
    {source opposite : CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : LocalQuotientContext source opposite ambient) :
      Rat.Fraction.Rational :=
  (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient) / context.oppositeMargin

/-- The protected quotient-residual coefficient is positive. -/
theorem targetCoefficient_pos
    {source opposite : CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : LocalQuotientContext source opposite ambient) :
    0 < targetCoefficient context := by
  exact Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos source ambient))
    context.oppositeMargin_pos

/-- The displayed quotient-residual estimate factors as its target coefficient times epsilon squared. -/
theorem targetCoefficient_mul_epsilon_sq
    {source opposite : CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : LocalQuotientContext source opposite ambient)
    (epsilon : Rat.Fraction.Rational) :
    (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2) /
        context.oppositeMargin =
      targetCoefficient context * epsilon ^ 2 := by
  unfold targetCoefficient
  rw [Rat.Fraction.Field.div_eq_mul_inv_direct,
    Rat.Fraction.Field.div_eq_mul_inv_direct]
  calc
    (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * epsilon ^ 2) *
        context.oppositeMargin⁻¹ =
        (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient) *
          (epsilon ^ 2 * context.oppositeMargin⁻¹) :=
      Rat.Fraction.Field.mul_assoc _ _ _
    _ = (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient) *
          (context.oppositeMargin⁻¹ * epsilon ^ 2) := by
      exact congrArg
        (fun value => (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient) * value)
        (Rat.Fraction.Field.mul_comm _ _)
    _ = (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient *
          context.oppositeMargin⁻¹) * epsilon ^ 2 :=
      (Rat.Fraction.Field.mul_assoc _ _ _).symm
end

end Purelib.RationalFunctions.Approximation.Height.Budget

end
