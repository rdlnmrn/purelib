module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Proportions.QuadTriple.IsoscelesAlternatives
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Isosceles.BasePoint.Product
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic

open Purelib.Algebra

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace Purelib.Geometry.Triangles.Equilateral.BasePoint.Alternatives

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The geometric interface to Exercise 11.6: an equilateral triangle and a displayed point on its non-null base supply
both scalar premises above. -/
theorem exercise_11_6_geometric [Nontrivial K]
  [DecidableEq K]
    (first second vertex point : Purelib.Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (baseNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (pointOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains point)
    (firstLegEqualsBase :
      Quadrance.quadrance first vertex = Quadrance.quadrance first second)
    (equalLegs :
      Quadrance.quadrance first vertex = Quadrance.quadrance second vertex) :
    Quadrance.quadrance first second =
        2 * Quadrance.quadrance vertex point - Quadrance.quadrance first point -
          Quadrance.quadrance second point ∨
      Quadrance.quadrance first second =
        (2 * Quadrance.quadrance vertex point + Quadrance.quadrance first point +
          Quadrance.quadrance second point) / 3 := by
  have collinear : Incidence.Collinear first second point :=
    ⟨Incidence.lineThrough first second firstSecondDistinct,
      Incidence.lineThrough_contains_first first second firstSecondDistinct,
      Incidence.lineThrough_contains_second first second firstSecondDistinct,
      pointOnBase⟩
  have baseTriple :
      Purelib.Geometry.Trigonometry.QuadTriple (Quadrance.quadrance second point) (Quadrance.quadrance first point)
        (Quadrance.quadrance first second) :=
    (Quadrea.Basic.triple_quad_formula first second point twoNonzero).2 collinear
  have isoscelesProduct := Isosceles.BasePoint.Product.exercise_11_5 first second vertex point
    firstSecondDistinct twoNonzero baseNonNull pointOnBase equalLegs
  rw [firstLegEqualsBase] at isoscelesProduct
  exact Proportions.QuadTriple.IsoscelesAlternatives.exercise_11_6 (Quadrance.quadrance first second)
    (Quadrance.quadrance first point)
    (Quadrance.quadrance second point) (Quadrance.quadrance vertex point) threeNonzero
    baseTriple isoscelesProduct
end Purelib.Geometry.Triangles.Equilateral.BasePoint.Alternatives

end
