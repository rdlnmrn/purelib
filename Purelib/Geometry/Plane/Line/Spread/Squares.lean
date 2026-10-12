module

import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Squares

variable {K : Type*} [ExplicitField K]

/-- The square condition in Theorem 45, expressed in the two equivalent finite forms used by the book and by the
normalized construction. -/
theorem spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second) :
    Squares.IsNonzeroSquare (Spread.spread first second firstNonNull secondNonNull) ↔
      Squares.IsNonzeroSquare (Line.Basic.lineNorm first * Line.Basic.lineNorm second) := by
  unfold Spread.spread
  exact Squares.quotient_square_isNonzeroSquare_iff
    (first.a * second.b - second.a * first.b)
    (Line.Basic.lineNorm first * Line.Basic.lineNorm second)
    (Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel)
    (ExplicitField.mul_ne_zero firstNonNull secondNonNull)

/-- Equal spreads with a non-null third line give equality of the norm-scaled squared direction determinants.

All three lines are non-null so the common bisector norm and both spread denominators may be cancelled. -/
public theorem
  equal_spreads_norm_balance [DecidableEq
  K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (bisectorNonNull : ¬ bisector.IsNull)
    (equalSpreads :
      Spread.spread first bisector firstNonNull bisectorNonNull =
        Spread.spread second bisector secondNonNull bisectorNonNull) :
    Line.Basic.lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 =
      Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by
  have firstDenominatorNonzero :
      Line.Basic.lineNorm first * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero :
      Line.Basic.lineNorm second * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  unfold Spread.spread at equalSpreads
  have crossProduct := (fun {K : Type _} [ExplicitField K] [DecidableEq K] {leftNumerator
    rightNumerator leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero :
    rightDenominator ≠ 0) (ratiosEqual : leftNumerator / leftDenominator = rightNumerator / rightDenominator) =>
    (Purelib.Algebra.Field.Ratio.cross_product_of_ratio_eq (K := K) (leftNumerator := leftNumerator) (rightNumerator :=
    rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero rightNonzero
    ratiosEqual : leftNumerator * rightDenominator = rightNumerator * leftDenominator))
    firstDenominatorNonzero secondDenominatorNonzero equalSpreads
  have scaledDifference :
      (Line.Basic.lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2) *
        Line.Basic.lineNorm bisector = 0 := by
    calc
      (Line.Basic.lineNorm second *
            (first.a * bisector.b - bisector.a * first.b) ^ 2 -
          Line.Basic.lineNorm first *
            (second.a * bisector.b - bisector.a * second.b) ^ 2) *
          Line.Basic.lineNorm bisector =
        (first.a * bisector.b - bisector.a * first.b) ^ 2 *
            (Line.Basic.lineNorm second * Line.Basic.lineNorm bisector) -
          (second.a * bisector.b - bisector.a * second.b) ^ 2 *
            (Line.Basic.lineNorm first * Line.Basic.lineNorm bisector) := by ring1
      _ = 0 := by rw [crossProduct]; ring1
  have differenceZero :
      Line.Basic.lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 = 0 := by
    apply ExplicitField.eq_of_mul_eq_mul_right
      (show Line.Basic.lineNorm bisector ≠ 0 from bisectorNonNull)
    simpa only [zero_mul] using scaledDifference
  calc
    Line.Basic.lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 =
      (Line.Basic.lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2) +
        Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by ring1
    _ = Line.Basic.lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by
      rw [differenceZero]
      ring1

/-- Equal spreads against a non-null third line explicitly exhibit the product of the first two line norms as a square.
The returned root is `‖first‖ det(second,bisector) / det(first,bisector)`. -/
theorem normProduct_isNonzeroSquare_of_equal_spreads [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (bisectorNonNull : ¬ bisector.IsNull)
    (notParallel : ¬ first.Parallel second)
    (equalSpreads :
      Spread.spread first bisector firstNonNull bisectorNonNull =
        Spread.spread second bisector secondNonNull bisectorNonNull) :
    Squares.IsNonzeroSquare (Basic.lineNorm first * Basic.lineNorm second) := by
  let firstCross := first.a * bisector.b - bisector.a * first.b
  let secondCross := second.a * bisector.b - bisector.a * second.b
  have normBalance :
      Basic.lineNorm second * firstCross ^ 2 =
        Basic.lineNorm first * secondCross ^ 2 := by
    exact equal_spreads_norm_balance first second
      bisector firstNonNull
      secondNonNull bisectorNonNull equalSpreads
  have firstCrossNonzero : firstCross ≠ 0 := by
    intro firstCrossZero
    have secondCrossSquareZero : secondCross ^ 2 = 0 := by
      have scaledZero : Basic.lineNorm first * secondCross ^ 2 = 0 := by
        calc
          Basic.lineNorm first * secondCross ^ 2 =
              Basic.lineNorm second * firstCross ^ 2 := normBalance.symm
          _ = 0 := by rw [firstCrossZero]; ring1
      exact ExplicitField.eq_zero_of_mul_eq_zero_left firstNonNull scaledZero
    have secondCrossZero : secondCross = 0 := by
      by_cases crossZero : secondCross = 0
      · exact crossZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero crossZero crossZero) (by
            simpa [pow_two] using secondCrossSquareZero))
    have determinantTimesNormZero :
        (first.a * second.b - second.a * first.b) *
          Basic.lineNorm bisector = 0 := by
      calc
        (first.a * second.b - second.a * first.b) *
            Basic.lineNorm bisector =
          firstCross *
              (second.a * bisector.a + second.b * bisector.b) -
            secondCross *
              (first.a * bisector.a + first.b * bisector.b) := by
                unfold firstCross secondCross Basic.lineNorm
                ring1
        _ = 0 := by rw [firstCrossZero, secondCrossZero]; ring1
    exact (ExplicitField.mul_ne_zero
      (Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel)
      (show Basic.lineNorm bisector ≠ 0 from bisectorNonNull))
      determinantTimesNormZero
  have secondCrossNonzero : secondCross ≠ 0 := by
    intro secondCrossZero
    have firstCrossSquareNonzero : firstCross ^ 2 ≠ 0 := by
      simpa [pow_two] using
        (ExplicitField.mul_ne_zero firstCrossNonzero firstCrossNonzero)
    exact (ExplicitField.mul_ne_zero secondNonNull
      firstCrossSquareNonzero) (by
        calc
          Basic.lineNorm second * firstCross ^ 2 =
              Basic.lineNorm first * secondCross ^ 2 := normBalance
          _ = 0 := by rw [secondCrossZero]; ring1)
  have firstCrossSquareNonzero : firstCross ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (ExplicitField.mul_ne_zero firstCrossNonzero firstCrossNonzero)
  refine ⟨Basic.lineNorm first * secondCross / firstCross,
    ExplicitField.div_ne_zero
      (ExplicitField.mul_ne_zero firstNonNull secondCrossNonzero)
      firstCrossNonzero, ?_⟩
  apply ExplicitField.eq_of_mul_eq_mul_right firstCrossSquareNonzero
  calc
    (Basic.lineNorm first * Basic.lineNorm second) * firstCross ^ 2 =
        Basic.lineNorm first * (Basic.lineNorm second * firstCross ^ 2) := by ring1
    _ = Basic.lineNorm first * (Basic.lineNorm first * secondCross ^ 2) := by
      rw [normBalance]
    _ = (Basic.lineNorm first * secondCross) ^ 2 := by ring1
    _ =
        ((Basic.lineNorm first * secondCross / firstCross) * firstCross) ^ 2 := by
      rw [ExplicitField.div_mul_cancel
        (Basic.lineNorm first * secondCross) firstCrossNonzero]
    _ = (Basic.lineNorm first * secondCross / firstCross) ^ 2 *
        firstCross ^ 2 := by ring1
end Purelib.Geometry.Plane.Line.Spread.Squares

end
