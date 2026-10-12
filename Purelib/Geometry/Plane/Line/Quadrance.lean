module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Quadrance

/-- Theorem 19 (Null line): the line through two distinct points is null exactly when their quadrance is zero. -/
theorem null_line_iff_quadrance_zero [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (Incidence.lineThrough first second distinct).IsNull ↔ Quadrance.quadrance first second = 0 := by
  unfold IsNull Incidence.lineThrough Quadrance.quadrance
  constructor <;> intro equality
  · calc
      (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 := by ring1
      _ = 0 := equality
  · calc
      (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
          (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by ring1
      _ = 0 := equality

end Purelib.Geometry.Plane.Line.Quadrance

end

end

end

section
public section

/-!
# Divine Proportions, §12.1: the Extended spread law

The book proves the result by introducing the three side midpoints and then
solving an auxiliary triangle.  Here the same finite content is exposed by a
stronger polynomial lemma: a triangle with a displayed common-quadrance center
satisfies `quadrea * circumquadrance = Q₁ * Q₂ * Q₃`.  Combining that identity
with Quadrea spread gives the final reciprocal, while the ordinary Spread law
gives the other two equalities.

No generic-position choice among the midpoints is needed, and all divisions
are guarded by explicit nonzero certificates.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Geometry.Plane.Line.Quadrance
/-- Distinct endpoints of a non-null line have nonzero quadrance. -/
private theorem side_quadrance_nonzero [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    Quadrance.quadrance first second ≠ 0 := by
  intro quadranceZero
  exact nonNull
    ((Geometry.Plane.Line.Quadrance.null_line_iff_quadrance_zero first second distinct).2 quadranceZero)
end Purelib.Geometry.Plane.Line.Quadrance

end

end

end

section
public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Polygons.CornerTriangle

/-- Distinct endpoints of a non-null line have nonzero quadrance. -/
private theorem quadrance_ne_zero_of_line_nonNull [DecidableEq K]
    (first second : Plane.Point K) (distinct : first ≠ second)
    (lineNonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    Quadrance.quadrance first second ≠ 0 := by
  intro quadranceZero
  apply lineNonNull
  exact (Geometry.Plane.Line.Quadrance.null_line_iff_quadrance_zero first second distinct).2 quadranceZero

end Purelib.Geometry.Polygons.CornerTriangle

end

end

section
public section

/-!
# Divine Proportions, §5.4: quadrance to a line

Both results are proved directly from the finite coordinate formulas.  They
therefore apply unchanged to finite fields, subject only to the displayed
nonzero denominators.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Quadrance

/-- Quadrance from a point to a displayed non-null line. -/
@[expose] def pointLineQuadrance (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) : K :=
  Quadrance.quadrance point (Altitude.altitudeFoot point line nonNull)

/-- Theorem 25 (Quadrance to a line): the altitude-foot construction evaluates to the source's rational expression. -/
theorem pointLineQuadrance_formula
    (point : Point K) (line : Line K) (nonNull : ¬ line.IsNull) :
    Quadrance.pointLineQuadrance point line nonNull =
      (line.a * point.x + line.b * point.y + line.c) ^ 2 /
        Basic.lineNorm line := by
  have normNonzero : Basic.lineNorm line ≠ 0 := nonNull
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  have xDifference :
      (line.b ^ 2 * point.x - line.a * line.b * point.y -
          line.a * line.c) * (Basic.lineNorm line)⁻¹ - point.x =
        -line.a * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹ := by
    calc
      (line.b ^ 2 * point.x - line.a * line.b * point.y -
            line.a * line.c) * (Basic.lineNorm line)⁻¹ - point.x =
        -line.a * (line.a * point.x + line.b * point.y + line.c) *
            (Basic.lineNorm line)⁻¹ -
          point.x * (1 - Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
            unfold Basic.lineNorm
            ring1
      _ = -line.a * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹ := by rw [normCancel]; ring1
  have yDifference :
      (-line.a * line.b * point.x + line.a ^ 2 * point.y -
          line.b * line.c) * (Basic.lineNorm line)⁻¹ - point.y =
        -line.b * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹ := by
    calc
      (-line.a * line.b * point.x + line.a ^ 2 * point.y -
            line.b * line.c) * (Basic.lineNorm line)⁻¹ - point.y =
        -line.b * (line.a * point.x + line.b * point.y + line.c) *
            (Basic.lineNorm line)⁻¹ -
          point.y * (1 - Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
            unfold Basic.lineNorm
            ring1
      _ = -line.b * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹ := by rw [normCancel]; ring1
  unfold Quadrance.pointLineQuadrance Quadrance.quadrance Altitude.altitudeFoot
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [xDifference, yDifference]
  calc
    ((-line.a * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹) ^ 2 +
      (-line.b * (line.a * point.x + line.b * point.y + line.c) *
          (Basic.lineNorm line)⁻¹) ^ 2) =
      (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) *
        ((line.a * point.x + line.b * point.y + line.c) ^ 2 *
          (Basic.lineNorm line)⁻¹) := by
            unfold Basic.lineNorm
            ring1
    _ = (line.a * point.x + line.b * point.y + line.c) ^ 2 *
        (Basic.lineNorm line)⁻¹ := by rw [normCancel, one_mul]

end Purelib.Geometry.Plane.Line.Quadrance

end

end

end

section
public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Quadrance

/-- The line-through construction has norm equal to endpoint quadrance. -/
theorem lineThrough_norm_eq_quadrance [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    Basic.lineNorm (Incidence.lineThrough first second distinct) = Quadrance.quadrance first second := by
  unfold Basic.lineNorm Incidence.lineThrough Quadrance.quadrance
  ring1

end Purelib.Geometry.Plane.Line.Quadrance

end

end

section
public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Trigonometry.TriangleRatios

/-- Distinct endpoints of a non-null line have nonzero quadrance. -/
public theorem quadrance_ne_zero_of_line_nonNull [DecidableEq K]
    (first second : Plane.Point K) (distinct : first ≠ second)
    (nonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    Quadrance.quadrance first second ≠ 0 := by
  intro quadranceZero
  exact nonNull
    ((Geometry.Plane.Line.Quadrance.null_line_iff_quadrance_zero first second distinct).2 quadranceZero)

end Purelib.Geometry.Trigonometry.TriangleRatios

end

end

end
