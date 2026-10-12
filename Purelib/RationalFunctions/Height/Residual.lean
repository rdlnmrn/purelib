module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Degree
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial
import Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator
public import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.RationalFunctions.Residual.Local.Bounds
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

namespace Purelib.RationalFunctions.Height.Residual

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- A nonzero protected quotient residual has a necessary denominator-height lower bound.

The Gaussian fraction lies in a source state refining the protected box, and its source evaluation is nonzero.
Coefficient scale squared, fraction height to source degree and the opposite majorant multiply the quotient residual to
at least one. -/
theorem one_le_scaled_height_mul_quotientResidual
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Rational.Box}
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (fraction : Gaussian.Basic.Canonical.Fraction.NaturalDenominator) (inside : state.box.Contains fraction.value)
    (sourceNonzero : source.eval fraction.value ≠ 0) :
    (1 : Rat.Fraction.Rational) ≤
      (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) ^ 2 *
        (fraction.height : Rat.Fraction.Rational) ^ source.natDegree *
          context.oppositeMajorant *
            Residual.Basic.quotientResidualSq
              source opposite fraction.value := by
  have sourceLower :=
    Dense.Gaussian.Residual.NaturalDenominator.one_le_scaled_height_mul_residual source
      (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos
        context.sourceDegreePositive)
      fraction sourceNonzero
  have sourceUpper :=
    context.sourceResidual_le_quotientResidualSq_mul_majorant
      refinesProtected inside
  have scalePositive : (0 : Rat.Fraction.Rational) <
      (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) :=
    Rat.Fraction.Cast.Order.natCast_pos_direct
      (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale_pos source)
  have heightPositiveNat : 0 < fraction.height := by
    exact Nat.pow_pos fraction.denominatorPositive
  have heightPositive : (0 : Rat.Fraction.Rational) < (fraction.height : Rat.Fraction.Rational) :=
    Rat.Fraction.Cast.Order.natCast_pos_direct heightPositiveNat
  have scaleNonnegative : (0 : Rat.Fraction.Rational) ≤
      (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) ^ 2 *
        (fraction.height : Rat.Fraction.Rational) ^ source.natDegree :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.pow_nonneg_direct
        scalePositive.le 2)
      (Rat.Fraction.Order.Arithmetic.pow_nonneg_direct
        heightPositive.le _)
  calc
    (1 : Rat.Fraction.Rational) ≤
        (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) ^ 2 *
          (fraction.height : Rat.Fraction.Rational) ^ source.natDegree *
            Gaussian.Norm.Basic.normSq (source.eval fraction.value) := sourceLower
    _ ≤
        ((Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) ^ 2 *
          (fraction.height : Rat.Fraction.Rational) ^ source.natDegree) *
            (Residual.Basic.quotientResidualSq
              source opposite fraction.value * context.oppositeMajorant) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceUpper
        scaleNonnegative
    _ =
        (Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale source : Rat.Fraction.Rational) ^ 2 *
          (fraction.height : Rat.Fraction.Rational) ^ source.natDegree *
            context.oppositeMajorant *
              Residual.Basic.quotientResidualSq
                source opposite fraction.value := by ring1
end Purelib.RationalFunctions.Height.Residual

end
