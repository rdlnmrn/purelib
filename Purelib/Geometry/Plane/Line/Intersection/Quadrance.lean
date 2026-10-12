module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

@[expose] public section

/-!
# Divine Proportions, Exercise 5.1

The quadrance between `l₁l₂` and `l₁l₃` is proved first after
clearing the two explicit line-intersection denominators.  The printed
quotient is then recovered by cancelling their nonzero squared product.  No
intersection, inverse, or projective representative is selected implicitly.
-/

namespace Purelib.Geometry.Plane.Line.Intersection.Quadrance

variable {K : Type*} [ExplicitField K]

/-- The denominator-cleared core of Exercise 5.1. The six-term factor is exactly the finite coefficient determinant of
the three displayed lines. -/
theorem exercise_5_1_cleared
    (first second third : Plane.Line K)
    (firstSecondNonparallel : ¬ first.Parallel second)
    (firstThirdNonparallel : ¬ first.Parallel third) :
    Quadrance.quadrance
          (Intersection.lineIntersection first second firstSecondNonparallel)
          (Intersection.lineIntersection first third firstThirdNonparallel) *
        ((first.a * second.b - second.a * first.b) ^ 2 *
          (first.a * third.b - third.a * first.b) ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        Incidence.lineDeterminant first second third ^ 2 := by
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstThirdDenominator :=
    first.a * third.b - third.a * first.b
  let firstSecondPoint :=
    Intersection.lineIntersection first second firstSecondNonparallel
  let firstThirdPoint :=
    Intersection.lineIntersection first third firstThirdNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstThirdDenominatorNonzero : firstThirdDenominator ≠ 0 := by
    exact firstThirdNonparallel
  have firstSecondXCancel :
      firstSecondPoint.x * firstSecondDenominator =
        first.b * second.c - second.b * first.c := by
    dsimp only [firstSecondPoint, Intersection.lineIntersection, firstSecondDenominator]
    exact ExplicitField.div_mul_cancel _
      firstSecondDenominatorNonzero
  have firstSecondYCancel :
      firstSecondPoint.y * firstSecondDenominator =
        first.c * second.a - second.c * first.a := by
    dsimp only [firstSecondPoint, Intersection.lineIntersection, firstSecondDenominator]
    exact ExplicitField.div_mul_cancel _
      firstSecondDenominatorNonzero
  have firstThirdXCancel :
      firstThirdPoint.x * firstThirdDenominator =
        first.b * third.c - third.b * first.c := by
    dsimp only [firstThirdPoint, Intersection.lineIntersection, firstThirdDenominator]
    exact ExplicitField.div_mul_cancel _
      firstThirdDenominatorNonzero
  have firstThirdYCancel :
      firstThirdPoint.y * firstThirdDenominator =
        first.c * third.a - third.c * first.a := by
    dsimp only [firstThirdPoint, Intersection.lineIntersection, firstThirdDenominator]
    exact ExplicitField.div_mul_cancel _
      firstThirdDenominatorNonzero
  have xDifferenceCleared :
      (firstThirdPoint.x - firstSecondPoint.x) *
          (firstSecondDenominator * firstThirdDenominator) =
        first.b * Incidence.lineDeterminant first second third := by
    calc
      (firstThirdPoint.x - firstSecondPoint.x) *
            (firstSecondDenominator * firstThirdDenominator) =
          (firstThirdPoint.x * firstThirdDenominator) *
              firstSecondDenominator -
            (firstSecondPoint.x * firstSecondDenominator) *
              firstThirdDenominator := by ring1
      _ = (first.b * third.c - third.b * first.c) *
              firstSecondDenominator -
            (first.b * second.c - second.b * first.c) *
              firstThirdDenominator := by
            rw [firstThirdXCancel, firstSecondXCancel]
      _ = first.b * Incidence.lineDeterminant first second third := by
            unfold firstSecondDenominator firstThirdDenominator
              Incidence.lineDeterminant
            ring1
  have yDifferenceCleared :
      (firstThirdPoint.y - firstSecondPoint.y) *
          (firstSecondDenominator * firstThirdDenominator) =
        -first.a * Incidence.lineDeterminant first second third := by
    calc
      (firstThirdPoint.y - firstSecondPoint.y) *
            (firstSecondDenominator * firstThirdDenominator) =
          (firstThirdPoint.y * firstThirdDenominator) *
              firstSecondDenominator -
            (firstSecondPoint.y * firstSecondDenominator) *
              firstThirdDenominator := by ring1
      _ = (first.c * third.a - third.c * first.a) *
              firstSecondDenominator -
            (first.c * second.a - second.c * first.a) *
              firstThirdDenominator := by
            rw [firstThirdYCancel, firstSecondYCancel]
      _ = -first.a * Incidence.lineDeterminant first second third := by
            unfold firstSecondDenominator firstThirdDenominator
              Incidence.lineDeterminant
            ring1
  change
    Quadrance.quadrance firstSecondPoint firstThirdPoint *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        Incidence.lineDeterminant first second third ^ 2
  calc
    Quadrance.quadrance firstSecondPoint firstThirdPoint *
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
        ((firstThirdPoint.x - firstSecondPoint.x) *
            (firstSecondDenominator * firstThirdDenominator)) ^ 2 +
          ((firstThirdPoint.y - firstSecondPoint.y) *
            (firstSecondDenominator * firstThirdDenominator)) ^ 2 := by
              unfold Quadrance.quadrance
              ring1
    _ = (first.b * Incidence.lineDeterminant first second third) ^ 2 +
        (-first.a * Incidence.lineDeterminant first second third) ^ 2 := by
          rw [xDifferenceCleared, yDifferenceCleared]
    _ = (first.a ^ 2 + first.b ^ 2) *
        Incidence.lineDeterminant first second third ^ 2 := by ring1

/-- Exercise 5.1: the exact printed quadrance between the two intersections `l₁l₂` and `l₁l₃`. Its numerator is the norm
of `l₁` times the square of the three-line determinant, and both denominator factors carry their explicit nonparallel
certificates. -/
theorem exercise_5_1
    (first second third : Plane.Line K)
    (firstSecondNonparallel : ¬ first.Parallel second)
    (firstThirdNonparallel : ¬ first.Parallel third) :
    Quadrance.quadrance
        (Intersection.lineIntersection first second firstSecondNonparallel)
        (Intersection.lineIntersection first third firstThirdNonparallel) =
      ((first.a ^ 2 + first.b ^ 2) *
          Incidence.lineDeterminant first second third ^ 2) /
        ((first.a * second.b - second.a * first.b) ^ 2 *
          (first.a * third.b - third.a * first.b) ^ 2) := by
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstThirdDenominator :=
    first.a * third.b - third.a * first.b
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstThirdDenominatorNonzero : firstThirdDenominator ≠ 0 := by
    exact firstThirdNonparallel
  have firstSecondSquareNonzero : firstSecondDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero firstSecondDenominatorNonzero
        firstSecondDenominatorNonzero
  have firstThirdSquareNonzero : firstThirdDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero firstThirdDenominatorNonzero
        firstThirdDenominatorNonzero
  have denominatorNonzero :
      firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2 ≠ 0 :=
    ExplicitField.mul_ne_zero firstSecondSquareNonzero
      firstThirdSquareNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  change
    Quadrance.quadrance
          (Intersection.lineIntersection first second firstSecondNonparallel)
          (Intersection.lineIntersection first third firstThirdNonparallel) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (((first.a ^ 2 + first.b ^ 2) *
          Incidence.lineDeterminant first second third ^ 2) /
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)) *
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)
  calc
    Quadrance.quadrance
          (Intersection.lineIntersection first second firstSecondNonparallel)
          (Intersection.lineIntersection first third firstThirdNonparallel) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        Incidence.lineDeterminant first second third ^ 2 := by
          unfold firstSecondDenominator firstThirdDenominator
          exact exercise_5_1_cleared first second third
            firstSecondNonparallel firstThirdNonparallel
    _ = (((first.a ^ 2 + first.b ^ 2) *
            Incidence.lineDeterminant first second third ^ 2) /
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) :=
      (ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end Purelib.Geometry.Plane.Line.Intersection.Quadrance

end
