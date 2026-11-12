module

public import Purelib.Geometry.Rational.Box.Outside.Sum
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Root displacement between two retained radicands

The original two square residuals and radicand movement bound the difference
of squares. A positive sum floor then bounds the root displacement. An
original zero-separated box supplies that floor for two contained readings,
without identifying either reading or its radicand with the other.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootProvenance

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)

/-- Two original square residuals and their radicand displacement bound the difference of squares. -/
theorem square_difference_le (first last firstParameter lastParameter : Canonical)
    {firstError movement lastError : Rational}
    (firstResidual : Norm.Basic.normSq (first * first - firstParameter) ≤ firstError)
    (parameterMovement : Norm.Basic.normSq (firstParameter - lastParameter) ≤ movement)
    (lastResidual : Norm.Basic.normSq (last * last - lastParameter) ≤ lastError) :
    Norm.Basic.normSq (first * first - last * last) ≤ 2 * (firstError + 2 * (movement + lastError)) := by
  have inner := (Norm.Bounds.normSq_sub_le_two
    (firstParameter - lastParameter) (last * last - lastParameter)).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct parameterMovement lastResidual) (by decide +kernel))
  have identity : first * first - last * last =
      (first * first - firstParameter) + ((firstParameter - lastParameter) -
        (last * last - lastParameter)) := by ring1
  exact (congrArg Norm.Basic.normSq identity).trans_le
    ((Norm.Bounds.normSq_add_le_two _ _).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct firstResidual inner) (by decide +kernel)))

/-- A positive sum floor converts the original residual and radicand bounds into a root-displacement bound.

The radicands remain independent. Multiplication of the root difference
and root sum gives their actual difference of squares; only the supplied
positive scalar floor is cancelled.
-/
theorem root_difference_le (first last firstParameter lastParameter : Canonical)
    {firstError movement lastError lower : Rational} (positive : 0 < lower)
    (sumLower : lower ≤ Norm.Basic.normSq (first + last))
    (firstResidual : Norm.Basic.normSq (first * first - firstParameter) ≤ firstError)
    (parameterMovement : Norm.Basic.normSq (firstParameter - lastParameter) ≤ movement)
    (lastResidual : Norm.Basic.normSq (last * last - lastParameter) ≤ lastError) :
    Norm.Basic.normSq (first - last) ≤ (2 * (firstError + 2 * (movement + lastError))) / lower := by
  apply Order.Arithmetic.le_of_mul_le_mul_right_direct (c := lower) _ positive
  have product : Norm.Basic.normSq (first - last) * Norm.Basic.normSq (first + last) =
      Norm.Basic.normSq (first * first - last * last) :=
    (Norm.Basic.normSq_mul _ _).symm.trans
      (congrArg Norm.Basic.normSq (show (first - last) * (first + last) =
        first * first - last * last by ring1))
  exact ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumLower (Norm.Basic.normSq_nonneg _)).trans_eq
    product).trans
      ((square_difference_le first last firstParameter lastParameter
        firstResidual parameterMovement lastResidual).trans_eq
        (Field.div_mul_cancel_of_ne _ lower positive.ne').symm)

/-- Two readings in the same original zero-separated box have a computed cross-radicand displacement bound.

The retained outside side supplies its positive margin and the root-sum
floor. Both original containment witnesses, residuals and radicand movement
are consumed directly; no root equality or fixed-radicand premise is needed.
-/
theorem root_difference_in_box_le {box : Box} (side : box.OutsideSide 0)
    (first last firstParameter lastParameter : Canonical)
    (firstInside : box.Contains first) (lastInside : box.Contains last)
    {firstError movement lastError : Rational}
    (firstResidual : Norm.Basic.normSq (first * first - firstParameter) ≤ firstError)
    (parameterMovement : Norm.Basic.normSq (firstParameter - lastParameter) ≤ movement)
    (lastResidual : Norm.Basic.normSq (last * last - lastParameter) ≤ lastError) :
    Norm.Basic.normSq (first - last) ≤
      (2 * (firstError + 2 * (movement + lastError))) / (4 * side.margin) :=
  root_difference_le first last firstParameter lastParameter
    (Order.Arithmetic.mul_pos_direct (by decide +kernel) side.margin_pos)
    (side.sum_normSq_lower firstInside lastInside) firstResidual parameterMovement lastResidual

end Purelib.Riemann.RootContinuation.SquareRootProvenance

end
