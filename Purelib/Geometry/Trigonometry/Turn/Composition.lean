module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

section
public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Trigonometry.Turn.Composition

variable {K : Type*} [ExplicitField K]

/-- The rational addition law for two successive turns. The operation is total as field arithmetic, while the geometric
theorem below carries the nonzero-denominator certificate needed for its intended quotient meaning. -/
@[expose] def turnComposition (first second : K) : K :=
  (first + second) / (1 - first * second)
end Purelib.Geometry.Trigonometry.Turn.Composition

end

section
public section

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

/-- The turn-composition parameter remains admissible whenever both input unit points and the composition denominator
are admissible. -/
theorem turnComposition_square_ne_negative_one
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (compositionDenominatorNonzero : 1 - left * right ≠ 0) :
    Geometry.Trigonometry.Turn.Composition.turnComposition left right ^ 2 ≠ -1 := by
  let leftDenominator := 1 + left ^ 2
  let rightDenominator := 1 + right ^ 2
  let compositionDenominator := 1 - left * right
  let compositionNumerator := left + right
  let composed := Geometry.Trigonometry.Turn.Composition.turnComposition left right
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have inputProductNonzero : leftDenominator * rightDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero leftDenominatorNonzero
      rightDenominatorNonzero
  have composedCancel : composed * compositionDenominator =
      compositionNumerator := by
    exact ExplicitField.div_mul_cancel compositionNumerator
      compositionDenominatorNonzero
  have denominatorIdentity :
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
        leftDenominator * rightDenominator := by
    calc
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
          compositionDenominator ^ 2 +
            (composed * compositionDenominator) ^ 2 := by ring1
      _ = compositionDenominator ^ 2 + compositionNumerator ^ 2 := by
        rw [composedCancel]
      _ = leftDenominator * rightDenominator := by
        unfold leftDenominator rightDenominator compositionDenominator
          compositionNumerator
        ring1
  apply (Conic.projectiveParameter_denominator_ne_zero_iff composed).1
  intro composedDenominatorZero
  apply inputProductNonzero
  calc
    leftDenominator * rightDenominator =
        (1 + composed ^ 2) * compositionDenominator ^ 2 :=
      denominatorIdentity.symm
    _ = 0 := by rw [composedDenominatorZero]; ring1
end

end Purelib.Curves.Plane.Conic

end

end
