module
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, Exercise 6.7

The twist analogue of the preceding Spread-from-points and Cross-from-points
theorems is a direct expansion of the two finite line coefficient triples.
-/

namespace Purelib.Geometry.Plane.Line.Twist

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Twist between two displayed non-perpendicular lines. -/
def twist (first second : Line K)
    (_notPerpendicular : ¬ first.Perpendicular second) : K :=
  (first.a * second.b - second.a * first.b) ^ 2 /
    (first.a * second.a + first.b * second.b) ^ 2

/-- Exercise 6.7: twist between the lines from `vertex` to `first` and `second`, written in the exact point-coordinate
form corresponding to Theorems 43 and 44. -/
theorem exercise_6_7 [DecidableEq K]
    (first second vertex : Point K)
    (firstDistinct : first ≠ vertex)
    (secondDistinct : second ≠ vertex)
    (notPerpendicular :
      ¬ (Incidence.lineThrough first vertex firstDistinct).Perpendicular
        (Incidence.lineThrough second vertex secondDistinct)) :
    twist
        (Incidence.lineThrough first vertex firstDistinct)
        (Incidence.lineThrough second vertex secondDistinct)
        notPerpendicular =
      (((first.y - vertex.y) * (vertex.x - second.x) -
          (second.y - vertex.y) * (vertex.x - first.x)) ^ 2) /
        (((first.y - vertex.y) * (second.y - vertex.y) +
          (vertex.x - first.x) * (vertex.x - second.x)) ^ 2) := by
  unfold twist Incidence.lineThrough
  ring1

end Purelib.Geometry.Plane.Line.Twist

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Plane.Line.Twist

variable {K : Type*} [ExplicitField K]

/-- Replacing both non-perpendicular lines by parallel representatives preserves twist. The proof keeps both denominator
certificates explicit and uses the finite direction scales supplied by the displayed line records. -/
theorem twist_eq_of_parallel_pairs [DecidableEq K]
    (first second firstParallel secondParallel : Plane.Line K)
    (firstNotPerpendicular : ¬ first.Perpendicular second)
    (parallelNotPerpendicular :
      ¬ firstParallel.Perpendicular secondParallel)
    (firstDirectionsParallel : first.Parallel firstParallel)
    (secondDirectionsParallel : second.Parallel secondParallel) :
    twist first second firstNotPerpendicular =
      twist firstParallel secondParallel parallelNotPerpendicular := by
  rcases Relations.direction_scale_of_parallel first firstParallel
      firstDirectionsParallel with
    ⟨firstScale, _firstScaleNonzero, firstA, firstB⟩
  rcases Relations.direction_scale_of_parallel second secondParallel
      secondDirectionsParallel with
    ⟨secondScale, _secondScaleNonzero, secondA, secondB⟩
  have firstDotNonzero :
      first.a * second.a + first.b * second.b ≠ 0 :=
    firstNotPerpendicular
  have parallelDotNonzero :
      firstParallel.a * secondParallel.a +
          firstParallel.b * secondParallel.b ≠ 0 :=
    parallelNotPerpendicular
  have firstDenominatorNonzero :
      (first.a * second.a + first.b * second.b) ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero firstDotNonzero firstDotNonzero
  have parallelDenominatorNonzero :
      (firstParallel.a * secondParallel.a +
          firstParallel.b * secondParallel.b) ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero parallelDotNonzero parallelDotNonzero
  unfold twist
  apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
    parallelDenominatorNonzero
  rw [firstA, firstB, secondA, secondB]
  ring1
end Purelib.Geometry.Plane.Line.Twist

end
