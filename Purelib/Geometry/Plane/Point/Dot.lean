module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
-- Exposed chord identities retain their explicit successor certificates.
public import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry
open scoped Purelib.Data.Nat

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

namespace Purelib.Geometry.Plane.Point.Dot

variable {K : Type*} [ExplicitField K]

/-- The dot product of the two vectors based at `origin`. -/
def pointVectorDot (origin first second : Plane.Point K) : K :=
  (first.x - origin.x) * (second.x - origin.x) +
    (first.y - origin.y) * (second.y - origin.y)
end Purelib.Geometry.Plane.Point.Dot

end

section
@[expose] public section

/-!
# Divine Proportions, §16.2: equal products

The source derives Theorem 106 from subtended spreads and the Spread law.  The
finite algebra underneath that proof is stronger: along any displayed chord,
the product of the two endpoint quadrances is the square of the intersection
point's circle-power.  This form needs no non-null hypotheses or division.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Equal circle radii express a chord quadrance as twice a displayed dot product based at one endpoint. -/
public theorem chordQuadrance_eq_twice_dot
    (center first second : Plane.Point K) (circleQuadrance : K)
    (firstRadius : Quadrance.quadrance first center = circleQuadrance)
    (secondRadius : Quadrance.quadrance second center = circleQuadrance) :
    Quadrance.quadrance first second =
      2 * ((first.x - second.x) * (center.x - second.x) +
        (first.y - second.y) * (center.y - second.y)) := by
  calc
    Quadrance.quadrance first second =
        Quadrance.quadrance first second + Quadrance.quadrance second center -
          circleQuadrance := by
      rw [secondRadius]
      ring1
    _ = Quadrance.quadrance first second + Quadrance.quadrance second center -
        Quadrance.quadrance first center := by rw [firstRadius]
    _ = 2 * ((first.x - second.x) * (center.x - second.x) +
        (first.y - second.y) * (center.y - second.y)) := by
      unfold Quadrance.quadrance
      ring1

end

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5 parallelogram exercises

The source's rectangle and rhombus conditions are retained as four finite
adjacent-side dot products and one finite diagonal dot product.  Their
connection with perpendicular displayed lines is proved without quotienting
line representatives.  Exercises 5.4--5.6 then follow from the coordinate-sum
form of the Parallelogram center theorem.
-/

namespace Purelib.Geometry.Plane.Point.Dot

variable {K : Type*} [ExplicitField K]

/-- Dot product of the directions of the displayed segments `AB` and `CD`. -/
def segmentDirectionDot
    (first second third fourth : Plane.Point K) : K :=
  (second.x - first.x) * (fourth.x - third.x) +
    (second.y - first.y) * (fourth.y - third.y)

/-- Segment-direction orthogonality is exactly perpendicularity of the two corresponding displayed lines. -/
theorem segmentDirectionDot_eq_zero_iff_perpendicular [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (thirdFourthDistinct : third ≠ fourth) :
    segmentDirectionDot first second third fourth = 0 ↔
      (Incidence.lineThrough first second firstSecondDistinct).Perpendicular
        (Incidence.lineThrough third fourth thirdFourthDistinct) := by
  unfold segmentDirectionDot Plane.Line.Perpendicular Incidence.lineThrough
  constructor <;> intro equality
  · calc
      (first.y - second.y) * (third.y - fourth.y) +
          (second.x - first.x) * (fourth.x - third.x) =
        (second.x - first.x) * (fourth.x - third.x) +
          (second.y - first.y) * (fourth.y - third.y) := by ring1
      _ = 0 := equality
  · calc
      (second.x - first.x) * (fourth.x - third.x) +
          (second.y - first.y) * (fourth.y - third.y) =
        (first.y - second.y) * (third.y - fourth.y) +
          (second.x - first.x) * (fourth.x - third.x) := by ring1
      _ = 0 := equality
end Purelib.Geometry.Plane.Point.Dot

end

end
