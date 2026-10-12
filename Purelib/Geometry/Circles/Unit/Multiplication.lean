module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Circles.Unit.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Gaussian
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The omitted denominator case has an exact geometric meaning: the product of the two admissible unit points is the
chart's excluded point `[-1,0]`. -/
theorem gaussianMul_unitCirclePoint_eq_excluded
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (compositionDenominatorZero : 1 - left * right = 0) :
    Conic.gaussianMul (Conic.unitCirclePoint left) (Conic.unitCirclePoint right) =
      Conic.unitCircleExcludedPoint := by
  let leftDenominator := 1 + left ^ 2
  let rightDenominator := 1 + right ^ 2
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have denominatorProductNonzero :
      leftDenominator * rightDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero leftDenominatorNonzero
      rightDenominatorNonzero
  have leftRealCancel :
      ((1 - left ^ 2) / leftDenominator) * leftDenominator =
        1 - left ^ 2 :=
    ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have leftImaginaryCancel :
      ((2 * left) / leftDenominator) * leftDenominator = 2 * left :=
    ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have rightRealCancel :
      ((1 - right ^ 2) / rightDenominator) * rightDenominator =
        1 - right ^ 2 :=
    ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have rightImaginaryCancel :
      ((2 * right) / rightDenominator) * rightDenominator = 2 * right :=
    ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have realNumerator :
      (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) =
        -(leftDenominator * rightDenominator) := by
    calc
      (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) =
        -(leftDenominator * rightDenominator) +
          2 * (1 - left * right) ^ 2 := by
            unfold leftDenominator rightDenominator
            ring1
      _ = -(leftDenominator * rightDenominator) := by
        rw [compositionDenominatorZero]
        ring1
  have imaginaryNumerator :
      (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) = 0 := by
    calc
      (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) =
        2 * (left + right) * (1 - left * right) := by ring1
      _ = 0 := by rw [compositionDenominatorZero]; ring1
  apply Plane.Point.ext
  · apply ExplicitField.eq_of_mul_eq_mul_right denominatorProductNonzero
    change
      (((1 - left ^ 2) / leftDenominator) *
          ((1 - right ^ 2) / rightDenominator) -
        ((2 * left) / leftDenominator) *
          ((2 * right) / rightDenominator)) *
          (leftDenominator * rightDenominator) =
        (-1 : K) * (leftDenominator * rightDenominator)
    calc
      (((1 - left ^ 2) / leftDenominator) *
            ((1 - right ^ 2) / rightDenominator) -
          ((2 * left) / leftDenominator) *
            ((2 * right) / rightDenominator)) *
            (leftDenominator * rightDenominator) =
        (((1 - left ^ 2) / leftDenominator) * leftDenominator) *
            (((1 - right ^ 2) / rightDenominator) * rightDenominator) -
          (((2 * left) / leftDenominator) * leftDenominator) *
            (((2 * right) / rightDenominator) * rightDenominator) := by ring1
      _ = (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) := by
        rw [leftRealCancel, rightRealCancel, leftImaginaryCancel,
          rightImaginaryCancel]
      _ = -(leftDenominator * rightDenominator) := realNumerator
      _ = (-1 : K) * (leftDenominator * rightDenominator) := by ring1
  · apply ExplicitField.eq_of_mul_eq_mul_right denominatorProductNonzero
    change
      (((1 - left ^ 2) / leftDenominator) *
          ((2 * right) / rightDenominator) +
        ((2 * left) / leftDenominator) *
          ((1 - right ^ 2) / rightDenominator)) *
          (leftDenominator * rightDenominator) =
        (0 : K) * (leftDenominator * rightDenominator)
    calc
      (((1 - left ^ 2) / leftDenominator) *
            ((2 * right) / rightDenominator) +
          ((2 * left) / leftDenominator) *
            ((1 - right ^ 2) / rightDenominator)) *
            (leftDenominator * rightDenominator) =
        (((1 - left ^ 2) / leftDenominator) * leftDenominator) *
            (((2 * right) / rightDenominator) * rightDenominator) +
          (((2 * left) / leftDenominator) * leftDenominator) *
            (((1 - right ^ 2) / rightDenominator) * rightDenominator) := by
          ring1
      _ = (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) := by
        rw [leftRealCancel, rightImaginaryCancel, leftImaginaryCancel,
          rightRealCancel]
      _ = 0 := imaginaryNumerator
      _ = (0 : K) * (leftDenominator * rightDenominator) := by ring1
end

end Purelib.Curves.Plane.Conic

end
