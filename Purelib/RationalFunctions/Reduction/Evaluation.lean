module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Reduction.Basic

section
@[expose] public section

/-!
# Finite cancellation for displayed rational functions

The executable extended Euclidean algorithm is run on normalized numerator
and denominator coefficient lists.  Its displayed common factor and two
cofactors are retained together with pointwise factorization identities,
finite degree balances, and a coprimality certificate for the reduced pair.
-/

namespace Purelib.RationalFunctions.Reduction.Basic
namespace ReducedPair

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Common-factor cancellation preserves the quotient at every non-pole point.

The original denominator evaluation is assumed nonzero. Its retained factorization proves nonzeroness of both the common
factor and reduced denominator before cancellation. -/
theorem quotient_eval_eq_reduced
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) (point : Gaussian.Basic.Canonical)
    (denominatorAtPoint : denominator.eval point ≠ 0) :
    numerator.eval point * (denominator.eval point)⁻¹ =
      reduced.numeratorReduced.eval point *
        (reduced.denominatorReduced.eval point)⁻¹ := by
  have commonAtPoint : reduced.common.eval point ≠ 0 := by
    intro commonZero
    apply denominatorAtPoint
    rw [reduced.denominator_eval point, commonZero, zero_mul]
  have reducedDenominatorAtPoint :
      reduced.denominatorReduced.eval point ≠ 0 := by
    intro reducedZero
    apply denominatorAtPoint
    rw [reduced.denominator_eval point, reducedZero, mul_zero]
  rw [reduced.numerator_eval point, reduced.denominator_eval point]
  let commonValue := reduced.common.eval point
  let numeratorValue := reduced.numeratorReduced.eval point
  let denominatorValue := reduced.denominatorReduced.eval point
  have productNonzero : commonValue * denominatorValue ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct
      commonAtPoint reducedDenominatorAtPoint
  apply Gaussian.Field.mul_right_cancel_of_ne productNonzero
  have leftCancel :
      (commonValue * numeratorValue *
          (commonValue * denominatorValue)⁻¹) *
          (commonValue * denominatorValue) =
        commonValue * numeratorValue := by
    have inverseProduct :
        (commonValue * denominatorValue)⁻¹ *
            (commonValue * denominatorValue) = 1 := by
      simpa only [Gaussian.Field.inv_eq] using
        Gaussian.Field.inv_mul
          (commonValue * denominatorValue) productNonzero
    rw [Gaussian.Basic.mul_assoc, inverseProduct,
      Gaussian.Basic.mul_one]
  have rightCancel :
      (numeratorValue * denominatorValue⁻¹) *
          (commonValue * denominatorValue) =
        commonValue * numeratorValue := by
    calc
      (numeratorValue * denominatorValue⁻¹) *
          (commonValue * denominatorValue) =
          (numeratorValue * denominatorValue⁻¹ * commonValue) *
            denominatorValue :=
        (Gaussian.Basic.mul_assoc _ _ _).symm
      _ = (commonValue *
          (numeratorValue * denominatorValue⁻¹)) * denominatorValue := by
        rw [Gaussian.Basic.mul_comm
          (numeratorValue * denominatorValue⁻¹) commonValue]
      _ = (commonValue * numeratorValue * denominatorValue⁻¹) *
          denominatorValue := by
        rw [← Gaussian.Basic.mul_assoc]
      _ = commonValue * numeratorValue *
          (denominatorValue⁻¹ * denominatorValue) :=
        Gaussian.Basic.mul_assoc _ _ _
      _ = commonValue * numeratorValue := by
        have inverseDenominator :
            denominatorValue⁻¹ * denominatorValue = 1 := by
          simpa only [Gaussian.Field.inv_eq] using
            Gaussian.Field.inv_mul denominatorValue
              reducedDenominatorAtPoint
        rw [inverseDenominator,
          Gaussian.Basic.mul_one]
  exact leftCancel.trans rightCancel.symm

end ReducedPair
end Purelib.RationalFunctions.Reduction.Basic

end
