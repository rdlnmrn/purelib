module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Rat.Sign.Typed.Sum
public import Purelib.Data.Sign.Sum
public import Purelib.Geometry.Rational.Plane.Turn.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Geometry.Rational.Plane.Turn.Product

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational.Plane

/-- Two slope-`1/3` factor turns make the product endpoint vectors have positive dot product.

The original two endpoint dot products are positive. Their retained
scaled cross-product bounds make the same cross-product product
strictly smaller than the dot-product product, proving the original
product vectors have positive dot product. -/
public theorem productComplexDot_pos_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Fraction.Rational}
    (left : Turn.Basic.NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (right : Turn.Basic.NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    0 <
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
      (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have leftDotPositive : 0 < leftDot :=
    Turn.Basic.complexDot_pos_of_narrowComplexTurn left
  have rightDotPositive : 0 < rightDot :=
    Turn.Basic.complexDot_pos_of_narrowComplexTurn right
  have leftBound : 3 * Fraction.abs (leftCross) < leftDot := by
    simpa only [leftCross, leftDot, Turn.Basic.NarrowComplexTurn] using left
  have rightBound : 3 * Fraction.abs (rightCross) < rightDot := by
    simpa only [rightCross, rightDot, Turn.Basic.NarrowComplexTurn] using right
  have crossProductLess : leftCross * rightCross < leftDot * rightDot := by
    by_cases leftCrossZero : leftCross = 0
    ·
      rw [leftCrossZero, zero_mul]
      exact Arithmetic.mul_pos_direct
        leftDotPositive rightDotPositive
    · by_cases rightCrossZero : rightCross = 0
      ·
        rw [rightCrossZero, mul_zero]
        exact Arithmetic.mul_pos_direct
          leftDotPositive rightDotPositive
      · have leftAbsPositive : 0 < Fraction.abs (leftCross) :=
          lt_of_le_of_ne (Arithmetic.abs_nonneg_direct _)
            (Ne.symm (Bounds.Abs.abs_ne_zero_direct leftCrossZero))
        have rightAbsPositive : 0 < Fraction.abs (rightCross) :=
          lt_of_le_of_ne (Arithmetic.abs_nonneg_direct _)
            (Ne.symm (Bounds.Abs.abs_ne_zero_direct rightCrossZero))
        have absProductPositive : 0 < Fraction.abs (leftCross) * Fraction.abs (rightCross) :=
          Arithmetic.mul_pos_direct
            leftAbsPositive rightAbsPositive
        have threeRightPositive : 0 < 3 * Fraction.abs (rightCross) :=
          Arithmetic.mul_pos_direct (by decide)
            rightAbsPositive
        calc
          leftCross * rightCross ≤ Fraction.abs (leftCross * rightCross) := Fraction.Order.Basic.le_max_left _ _
          _ = Fraction.abs (leftCross) * Fraction.abs (rightCross) :=
            Bounds.Abs.abs_mul_direct leftCross rightCross
          _ = 1 * (Fraction.abs (leftCross) * Fraction.abs (rightCross)) := by ring1
          _ < 9 * (Fraction.abs (leftCross) * Fraction.abs (rightCross)) :=
            Arithmetic.mul_lt_mul_of_pos_right_direct
              (by decide) absProductPositive
          _ = (3 * Fraction.abs (leftCross)) * (3 * Fraction.abs (rightCross)) := by ring1
          _ < leftDot * (3 * Fraction.abs (rightCross)) :=
            Arithmetic.mul_lt_mul_of_pos_right_direct
              leftBound threeRightPositive
          _ < leftDot * rightDot :=
            Arithmetic.mul_lt_mul_of_pos_left_direct
              leftDotPositive rightBound
  have identity :
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) =
        leftDot * rightDot - leftCross * rightCross := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring1
  rw [identity]
  exact Arithmetic.sub_pos_direct crossProductLess

/-- The oriented product turn is the sign-compatible sum of the two factor turns; the positive dot factors do not alter
either sign.

The positive original endpoint dot factors preserve each finite
cross-product sign. The same algebraic product-cross identity
transports formal sum compatibility to the original product turn. -/
public theorem productTurn_sumCompatible_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Fraction.Rational}
    (left : Turn.Basic.NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (right : Turn.Basic.NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    Data.Sign.SumCompatible
      (Data.Sign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ))
      (Data.Sign.ofCoordinate (Cₗ * Dᵣ - Dₗ * Cᵣ))
      (Data.Sign.ofCoordinate
        ((Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ))) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have leftDotPositive : 0 < leftDot :=
    Turn.Basic.complexDot_pos_of_narrowComplexTurn left
  have rightDotPositive : 0 < rightDot :=
    Turn.Basic.complexDot_pos_of_narrowComplexTurn right
  have sum := Data.Sign.sumCompatible_ofCoordinate
    (leftCross * rightDot) (leftDot * rightCross)
  have leftScale : Data.Sign.ofCoordinate (leftCross * rightDot) =
      Data.Sign.ofCoordinate leftCross := by
    rw [Data.Sign.ofCoordinate_mul,
      Data.Sign.ofCoordinate_of_pos rightDotPositive]
    cases Data.Sign.ofCoordinate leftCross <;> rfl
  have rightScale : Data.Sign.ofCoordinate (leftDot * rightCross) =
      Data.Sign.ofCoordinate rightCross := by
    rw [Data.Sign.ofCoordinate_mul,
      Data.Sign.ofCoordinate_of_pos leftDotPositive]
    cases Data.Sign.ofCoordinate rightCross <;> rfl
  have crossIdentity : leftCross * rightDot + leftDot * rightCross =
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
        (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring1
  rw [leftScale, rightScale, crossIdentity] at sum
  exact sum

end Purelib.Geometry.Rational.Plane.Turn.Product
