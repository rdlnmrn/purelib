module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Exercise 5.16

A triangle described by side lines has vertices `l₂l₃`, `l₃l₁`, and
`l₁l₂`.  The finite dual-determinant calculation below first proves that
the point determinant of those three explicit intersections, multiplied by
their three denominators, is the square of the line determinant.  Squaring
that identity gives the source's fourth-power quadrea formula.
-/

namespace Purelib.Geometry.Triangles.LineIntersection.Quadrea

variable {K : Type*} [ExplicitField K]

/-- The finite dual determinant underlying Exercise 5.16. Each vertex is an executable line intersection and each factor
on the left is its displayed nonzero denominator. -/
theorem lineTriangle_pointDeterminant_cleared
    (first second third : Plane.Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    Incidence.pointDeterminant
          (Intersection.lineIntersection second third secondThirdNonparallel)
          (Intersection.lineIntersection third first thirdFirstNonparallel)
          (Intersection.lineIntersection first second firstSecondNonparallel) *
        ((second.a * third.b - third.a * second.b) *
          (third.a * first.b - first.a * third.b) *
          (first.a * second.b - second.a * first.b)) =
      Incidence.lineDeterminant first second third ^ 2 := by
  let secondThirdDenominator :=
    second.a * third.b - third.a * second.b
  let thirdFirstDenominator :=
    third.a * first.b - first.a * third.b
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstPoint :=
    Intersection.lineIntersection second third secondThirdNonparallel
  let secondPoint :=
    Intersection.lineIntersection third first thirdFirstNonparallel
  let thirdPoint :=
    Intersection.lineIntersection first second firstSecondNonparallel
  have secondThirdDenominatorNonzero : secondThirdDenominator ≠ 0 := by
    exact secondThirdNonparallel
  have thirdFirstDenominatorNonzero : thirdFirstDenominator ≠ 0 := by
    exact thirdFirstNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstXCancel :
      firstPoint.x * secondThirdDenominator =
        second.b * third.c - third.b * second.c := by
    dsimp only [firstPoint, Intersection.lineIntersection, secondThirdDenominator]
    exact ExplicitField.div_mul_cancel _ secondThirdDenominatorNonzero
  have firstYCancel :
      firstPoint.y * secondThirdDenominator =
        second.c * third.a - third.c * second.a := by
    dsimp only [firstPoint, Intersection.lineIntersection, secondThirdDenominator]
    exact ExplicitField.div_mul_cancel _ secondThirdDenominatorNonzero
  have secondXCancel :
      secondPoint.x * thirdFirstDenominator =
        third.b * first.c - first.b * third.c := by
    dsimp only [secondPoint, Intersection.lineIntersection, thirdFirstDenominator]
    exact ExplicitField.div_mul_cancel _ thirdFirstDenominatorNonzero
  have secondYCancel :
      secondPoint.y * thirdFirstDenominator =
        third.c * first.a - first.c * third.a := by
    dsimp only [secondPoint, Intersection.lineIntersection, thirdFirstDenominator]
    exact ExplicitField.div_mul_cancel _ thirdFirstDenominatorNonzero
  have thirdXCancel :
      thirdPoint.x * firstSecondDenominator =
        first.b * second.c - second.b * first.c := by
    dsimp only [thirdPoint, Intersection.lineIntersection, firstSecondDenominator]
    exact ExplicitField.div_mul_cancel _ firstSecondDenominatorNonzero
  have thirdYCancel :
      thirdPoint.y * firstSecondDenominator =
        first.c * second.a - second.c * first.a := by
    dsimp only [thirdPoint, Intersection.lineIntersection, firstSecondDenominator]
    exact ExplicitField.div_mul_cancel _ firstSecondDenominatorNonzero
  change
    Incidence.pointDeterminant firstPoint secondPoint thirdPoint *
        (secondThirdDenominator * thirdFirstDenominator *
          firstSecondDenominator) =
      Incidence.lineDeterminant first second third ^ 2
  calc
    Incidence.pointDeterminant firstPoint secondPoint thirdPoint *
          (secondThirdDenominator * thirdFirstDenominator *
            firstSecondDenominator) =
        (firstPoint.x * secondThirdDenominator) *
            (secondPoint.y * thirdFirstDenominator) *
              firstSecondDenominator -
          (firstPoint.x * secondThirdDenominator) *
            (thirdPoint.y * firstSecondDenominator) *
              thirdFirstDenominator +
          (secondPoint.x * thirdFirstDenominator) *
            (thirdPoint.y * firstSecondDenominator) *
              secondThirdDenominator -
          (thirdPoint.x * firstSecondDenominator) *
            (secondPoint.y * thirdFirstDenominator) *
              secondThirdDenominator +
          (thirdPoint.x * firstSecondDenominator) *
            (firstPoint.y * secondThirdDenominator) *
              thirdFirstDenominator -
          (secondPoint.x * thirdFirstDenominator) *
            (firstPoint.y * secondThirdDenominator) *
              firstSecondDenominator := by
                unfold Incidence.pointDeterminant
                ring1
    _ = (second.b * third.c - third.b * second.c) *
            (third.c * first.a - first.c * third.a) *
              firstSecondDenominator -
          (second.b * third.c - third.b * second.c) *
            (first.c * second.a - second.c * first.a) *
              thirdFirstDenominator +
          (third.b * first.c - first.b * third.c) *
            (first.c * second.a - second.c * first.a) *
              secondThirdDenominator -
          (first.b * second.c - second.b * first.c) *
            (third.c * first.a - first.c * third.a) *
              secondThirdDenominator +
          (first.b * second.c - second.b * first.c) *
            (second.c * third.a - third.c * second.a) *
              thirdFirstDenominator -
          (third.b * first.c - first.b * third.c) *
            (second.c * third.a - third.c * second.a) *
              firstSecondDenominator := by
                rw [firstXCancel, firstYCancel, secondXCancel,
                  secondYCancel, thirdXCancel, thirdYCancel]
    _ = Incidence.lineDeterminant first second third ^ 2 := by
          unfold secondThirdDenominator thirdFirstDenominator
            firstSecondDenominator Incidence.lineDeterminant
          ring1

/-- The denominator-cleared quadrea formula of Exercise 5.16. -/
theorem exercise_5_16_cleared
    (first second third : Plane.Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    Quadrea.Basic.quadrea
          (Intersection.lineIntersection second third secondThirdNonparallel)
          (Intersection.lineIntersection third first thirdFirstNonparallel)
          (Intersection.lineIntersection first second firstSecondNonparallel) *
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) =
      4 * Incidence.lineDeterminant first second third ^ 4 := by
  let firstPoint :=
    Intersection.lineIntersection second third secondThirdNonparallel
  let secondPoint :=
    Intersection.lineIntersection third first thirdFirstNonparallel
  let thirdPoint :=
    Intersection.lineIntersection first second firstSecondNonparallel
  let denominatorProduct :=
    (second.a * third.b - third.a * second.b) *
      (third.a * first.b - first.a * third.b) *
      (first.a * second.b - second.a * first.b)
  have pointDeterminantCleared :=
    lineTriangle_pointDeterminant_cleared first second third
      secondThirdNonparallel thirdFirstNonparallel firstSecondNonparallel
  change
    Incidence.pointDeterminant firstPoint secondPoint thirdPoint * denominatorProduct =
      Incidence.lineDeterminant first second third ^ 2 at pointDeterminantCleared
  change
    Quadrea.Basic.quadrea firstPoint secondPoint thirdPoint *
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) =
      4 * Incidence.lineDeterminant first second third ^ 4
  rw [Quadrea.Basic.quadrea_coordinate_formula]
  calc
    4 * Incidence.pointDeterminant firstPoint secondPoint thirdPoint ^ 2 *
          ((second.a * third.b - third.a * second.b) ^ 2 *
            (third.a * first.b - first.a * third.b) ^ 2 *
            (first.a * second.b - second.a * first.b) ^ 2) =
        4 * (Incidence.pointDeterminant firstPoint secondPoint thirdPoint *
          denominatorProduct) ^ 2 := by
            unfold denominatorProduct
            ring1
    _ = 4 * (Incidence.lineDeterminant first second third ^ 2) ^ 2 := by
          rw [pointDeterminantCleared]
    _ = 4 * Incidence.lineDeterminant first second third ^ 4 := by ring1

/-- Exercise 5.16: the exact fourth-power formula for the quadrea of the triangle whose three displayed side lines are
`first`, `second`, and `third`. -/
theorem exercise_5_16
    (first second third : Plane.Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    Quadrea.Basic.quadrea
        (Intersection.lineIntersection second third secondThirdNonparallel)
        (Intersection.lineIntersection third first thirdFirstNonparallel)
        (Intersection.lineIntersection first second firstSecondNonparallel) =
      (4 * Incidence.lineDeterminant first second third ^ 4) /
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) := by
  let secondThirdDenominator :=
    second.a * third.b - third.a * second.b
  let thirdFirstDenominator :=
    third.a * first.b - first.a * third.b
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  have secondThirdDenominatorNonzero : secondThirdDenominator ≠ 0 := by
    exact secondThirdNonparallel
  have thirdFirstDenominatorNonzero : thirdFirstDenominator ≠ 0 := by
    exact thirdFirstNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have secondThirdSquareNonzero : secondThirdDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero secondThirdDenominatorNonzero
        secondThirdDenominatorNonzero
  have thirdFirstSquareNonzero : thirdFirstDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero thirdFirstDenominatorNonzero
        thirdFirstDenominatorNonzero
  have firstSecondSquareNonzero : firstSecondDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero firstSecondDenominatorNonzero
        firstSecondDenominatorNonzero
  have denominatorNonzero :
      secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2 ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero secondThirdSquareNonzero
        thirdFirstSquareNonzero)
      firstSecondSquareNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  change
    Quadrea.Basic.quadrea
          (Intersection.lineIntersection second third secondThirdNonparallel)
          (Intersection.lineIntersection third first thirdFirstNonparallel)
          (Intersection.lineIntersection first second firstSecondNonparallel) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) =
      ((4 * Incidence.lineDeterminant first second third ^ 4) /
          (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
            firstSecondDenominator ^ 2)) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2)
  calc
    Quadrea.Basic.quadrea
          (Intersection.lineIntersection second third secondThirdNonparallel)
          (Intersection.lineIntersection third first thirdFirstNonparallel)
          (Intersection.lineIntersection first second firstSecondNonparallel) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) =
      4 * Incidence.lineDeterminant first second third ^ 4 := by
        unfold secondThirdDenominator thirdFirstDenominator
          firstSecondDenominator
        exact exercise_5_16_cleared first second third
          secondThirdNonparallel thirdFirstNonparallel
          firstSecondNonparallel
    _ = ((4 * Incidence.lineDeterminant first second third ^ 4) /
          (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
            firstSecondDenominator ^ 2)) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) :=
      (ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end Purelib.Geometry.Triangles.LineIntersection.Quadrea

end
