module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Point.Quadrance.FourPoint
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

section
public section

/-!
# Divine Proportions, Theorem 115: the Four point relation

The Euler function is the explicitly expanded three-by-three determinant from
the source.  Its coordinate proof is a direct polynomial identity for four
displayed points in a two-dimensional plane.  Exercises 17.3--17.6 record the
alternative expansion, the finite Cayley--Menger determinant, the quadratic
form of the relation, and the circumquadrance deduction.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- Substituting equal circumquadrances into Euler's function yields twice the usual circumquadrance residual. -/
theorem eulerFunction_equal_radii (q₁ q₂ q₃ radius : K) :
    Quadrilateral.eulerFunction q₁ q₂ q₃ radius radius radius =
      2 * (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃) := by
  unfold Quadrilateral.eulerFunction Quadrilateral.determinantThree QuadTriple.Basic.archimedesFunction
  ring1

/-- The scalar form of Exercise 17.6: Euler's relation with three equal radii recovers the circumquadrance quotient. -/
theorem exercise_17_6_of_euler_relation
    (q₁ q₂ q₃ radius : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadreaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0)
    (relation : Quadrilateral.eulerFunction q₁ q₂ q₃ radius radius radius = 0) :
    radius = q₁ * q₂ * q₃ / QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
  have twiceResidualZero :
      2 * (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃) = 0 := by
    rw [← eulerFunction_equal_radii]
    exact relation
  have residualZero :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃ = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceResidualZero
  have productEquation :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ * radius =
        q₁ * q₂ * q₃ := Group.eq_of_sub_eq_zero residualZero
  apply ExplicitField.eq_of_mul_eq_mul_right quadreaNonzero
  calc
    radius * QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ =
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ * radius := by ring1
    _ = q₁ * q₂ * q₃ := productEquation
    _ = (q₁ * q₂ * q₃ / QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) *
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
      exact (ExplicitField.div_mul_cancel _ quadreaNonzero).symm

/-- Exercise 17.6 for an explicitly displayed circumcenter: applying the Four point relation to the center re-derives
the triangle circumquadrance formula without any completed or infinite object. -/
theorem exercise_17_6
    (first second third center : Plane.Point K) (radius : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadreaNonzero : Quadrea.Basic.quadrea first second third ≠ 0)
    (firstRadius : Quadrance.quadrance first center = radius)
    (secondRadius : Quadrance.quadrance second center = radius)
    (thirdRadius : Quadrance.quadrance third center = radius) :
    radius =
      Quadrance.quadrance second third * Quadrance.quadrance first third *
          Quadrance.quadrance first second / Quadrea.Basic.quadrea first second third := by
  have relation := Quadrilateral.four_point_relation first second third center
  rw [firstRadius, secondRadius, thirdRadius] at relation
  unfold Quadrea.Basic.quadrea at quadreaNonzero ⊢
  exact exercise_17_6_of_euler_relation
    (Quadrance.quadrance second third) (Quadrance.quadrance first third)
    (Quadrance.quadrance first second) radius twoNonzero quadreaNonzero relation

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

end
