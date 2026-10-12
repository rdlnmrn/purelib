module
import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Null
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Null

open Purelib.Geometry.Plane.Point

/-!
# Spread of non-null plane lines

Spread is the squared direction determinant divided by the product of the
nonzero direction norms. Parallel representatives, endpoint reversal and
line exchange preserve this scalar; incidence and quadrance give its
coordinate expression for lines through displayed points.
-/

public section
namespace Purelib.Geometry.Plane.Line.Spread

variable {K : Type*} [ExplicitField K]

/-- The product of the direction norms of two non-null lines is nonzero. -/
public theorem normProductNonzero
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Line.Basic.lineNorm first * Line.Basic.lineNorm second ≠ 0 :=
  Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull

/-- Spread between two displayed non-null lines. -/
@[expose] def spread (first second : Line K)
    (_firstNonNull : ¬ first.IsNull) (_secondNonNull : ¬ second.IsNull) : K :=
  (first.a * second.b - second.a * first.b) ^ 2 /
    (Line.Basic.lineNorm first * Line.Basic.lineNorm second)

/-- Replacing both non-null lines by parallel representatives preserves spread. -/
theorem spread_eq_of_parallel_pairs [DecidableEq K]
    (first second firstParallel secondParallel : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (firstParallelNonNull : ¬ firstParallel.IsNull)
    (secondParallelNonNull : ¬ secondParallel.IsNull)
    (firstDirectionsParallel : first.Parallel firstParallel)
    (secondDirectionsParallel : second.Parallel secondParallel) :
    Spread.spread first second firstNonNull secondNonNull =
      Spread.spread firstParallel secondParallel firstParallelNonNull
        secondParallelNonNull := by
  rcases Relations.direction_scale_of_parallel first firstParallel
      firstDirectionsParallel with
    ⟨firstScale, firstScaleNonzero, firstA, firstB⟩
  rcases Relations.direction_scale_of_parallel second secondParallel
      secondDirectionsParallel with
    ⟨secondScale, secondScaleNonzero, secondA, secondB⟩
  have firstDenominatorNonzero : Basic.lineNorm first * Basic.lineNorm second ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have secondDenominatorNonzero :
      Basic.lineNorm firstParallel * Basic.lineNorm secondParallel ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstParallelNonNull secondParallelNonNull
  unfold Spread.spread
  apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
    secondDenominatorNonzero
  unfold Basic.lineNorm
  rw [firstA, firstB, secondA, secondB]
  ring1

/-- A spread of two non-null lines vanishes exactly when their direction determinant vanishes. -/
theorem spread_eq_zero_iff_parallel [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Geometry.Plane.Line.Spread.spread first second firstNonNull secondNonNull = 0 ↔
      first.Parallel second := by
  let determinant := first.a * second.b - second.a * first.b
  let denominator := Line.Basic.lineNorm first * Line.Basic.lineNorm second
  have denominatorNonzero : denominator ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  constructor
  · intro spreadZero
    change determinant ^ 2 / denominator = 0 at spreadZero
    have numeratorZero : determinant ^ 2 = 0 := by
      calc
        determinant ^ 2 =
            (determinant ^ 2 / denominator) * denominator :=
              (Algebra.Field.ExplicitField.div_mul_cancel
                (determinant ^ 2) denominatorNonzero).symm
        _ = 0 := by
          rw [spreadZero]
          ring1
    have determinantZero : determinant = 0 := by
      by_cases zero : determinant = 0
      · exact zero
      · exact False.elim
          ((Algebra.Field.ExplicitField.mul_ne_zero zero zero) (by
            simpa [pow_two] using numeratorZero))
    exact determinantZero
  · intro parallel
    change determinant = 0 at parallel
    change determinant ^ 2 / denominator = 0
    rw [parallel]
    rw [show (0 : K) ^ 2 = 0 by ring1]
    exact Algebra.Field.ExplicitField.zero_div denominator

/-- Theorem 43 (Spread from points), in coordinate form. -/
theorem spread_from_points [DecidableEq K]
    (first second vertex : Point K)
    (firstDistinct : first ≠ vertex) (secondDistinct : second ≠ vertex)
    (firstNonNull : ¬ (Incidence.lineThrough first vertex firstDistinct).IsNull)
    (secondNonNull : ¬ (Incidence.lineThrough second vertex secondDistinct).IsNull) :
    Spread.spread (Incidence.lineThrough first vertex firstDistinct)
        (Incidence.lineThrough second vertex secondDistinct) firstNonNull secondNonNull =
      (((first.y - vertex.y) * (vertex.x - second.x) -
        (second.y - vertex.y) * (vertex.x - first.x)) ^ 2) /
        (Quadrance.quadrance first vertex * Quadrance.quadrance second vertex) := by
  unfold Spread.spread
  rw [Quadrance.lineThrough_norm_eq_quadrance first vertex firstDistinct,
    Quadrance.lineThrough_norm_eq_quadrance second vertex secondDistinct]
  congr 1

/-- Reversing both endpoint orders preserves the spread of two non-null lines. -/
private theorem spread_lineThrough_reverse_both [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull) :
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
        (Incidence.lineThrough third first firstThirdDistinct.symm)
        (Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull first second firstSecondDistinct firstSecondNonNull)
        (Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull first third firstThirdDistinct firstThirdNonNull) := by
  unfold Spread.spread Basic.lineNorm Incidence.lineThrough
  congr 1 <;> ring1

/-- Reversing both endpoint orders preserves the spread of two non-null lines. -/
public theorem spread_reverse_both [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull) :
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
        (Incidence.lineThrough third first firstThirdDistinct.symm)
        (by
          exact Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull
            first second firstSecondDistinct firstSecondNonNull)
        (by
          exact Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull
            first third firstThirdDistinct firstThirdNonNull) := by
  unfold Spread.spread Basic.lineNorm Incidence.lineThrough
  congr 1 <;> ring1

/-- Spread is symmetric in its two lines. -/
theorem spread_symm (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Spread.spread first second firstNonNull secondNonNull =
      Spread.spread second first secondNonNull firstNonNull := by
  unfold Spread.spread
  congr 1 <;> ring1

end Purelib.Geometry.Plane.Line.Spread

namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Reversing both endpoint orders preserves the spread of two non-null lines. -/
theorem spread_lineThrough_reverse_both
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull) :
    Spread.spread
        (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Spread.spread
        (Incidence.lineThrough second first firstSecondDistinct.symm)
        (Incidence.lineThrough third first firstThirdDistinct.symm)
        (by
          intro reversedNull
          apply firstSecondNonNull
          apply (Quadrance.null_line_iff_quadrance_zero first second
            firstSecondDistinct).2
          calc
            Quadrance.quadrance first second = Quadrance.quadrance second first :=
              Quadrance.quadrance_symm first second
            _ = 0 :=
              (Quadrance.null_line_iff_quadrance_zero second first
                firstSecondDistinct.symm).1 reversedNull)
        (by
          intro reversedNull
          apply firstThirdNonNull
          apply (Quadrance.null_line_iff_quadrance_zero first third
            firstThirdDistinct).2
          calc
            Quadrance.quadrance first third = Quadrance.quadrance third first :=
              Quadrance.quadrance_symm first third
            _ = 0 :=
              (Quadrance.null_line_iff_quadrance_zero third first
                firstThirdDistinct.symm).1 reversedNull) := by
  unfold Spread.spread Basic.lineNorm Incidence.lineThrough
  congr 1 <;> ring1

end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
