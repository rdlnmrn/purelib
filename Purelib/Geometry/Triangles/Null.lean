module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

@[expose] public section

/-!
# Divine Proportions, Exercises 3.11–3.12

A triangle is kept as three displayed points with explicit distinctness and
noncollinearity certificates.  Right vertices are perpendicularity equations
between its three finite side lines.  Null-side impossibility exposes the
book's standing characteristic-not-two assumption.
-/

namespace Purelib.Geometry.Triangles.Null

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 3.12: a noncollinear triangle cannot have all three sides null. The visible `2 ≠ 0` premise is the book's
standing characteristic boundary. -/
theorem not_all_sides_null [Nontrivial K] [DecidableEq K]
    (first second third : Purelib.Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ ((Incidence.lineThrough first second firstSecondDistinct).IsNull ∧
      (Incidence.lineThrough first third firstThirdDistinct).IsNull ∧
      (Incidence.lineThrough second third secondThirdDistinct).IsNull) := by
  rintro ⟨firstSideNull, thirdSideNull, secondSideNull⟩
  have firstQuadranceZero : Quadrance.quadrance first second = 0 :=
    (Quadrance.null_line_iff_quadrance_zero first second firstSecondDistinct).1
      firstSideNull
  have thirdQuadranceZero : Quadrance.quadrance first third = 0 :=
    (Quadrance.null_line_iff_quadrance_zero first third firstThirdDistinct).1
      thirdSideNull
  have secondQuadranceZero : Quadrance.quadrance second third = 0 :=
    (Quadrance.null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondSideNull
  apply notCollinear
  apply (Quadrea.Basic.triple_quad_formula first second third twoNonzero).1
  unfold Trigonometry.QuadTriple.Basic.archimedesFunction
  rw [firstQuadranceZero, thirdQuadranceZero, secondQuadranceZero]
  ring1

end Purelib.Geometry.Triangles.Null

end
