module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Triangles

/-!
# Divine Proportions, §13.1 and Theorem 91: finite plane isometries

An isometry carries both an executable point map and an executable inverse.
Its metric law is the finite equality asserting preservation of quadrance;
there is no completed space, infinite carrier argument, or selected inverse.

Theorem 91 follows exactly the source proof through the Triple-quad formula.
The hypothesis `2 ≠ 0` is exposed because over characteristic two the book's
quadrance degenerates and no longer detects collinearity.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Isometry.Basic.PlaneIsometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Isometries preserve the symmetric quadrea polynomial because they preserve each of its three quadrance inputs. -/
theorem preservesQuadrea (isometry :
  Isometry.Basic.PlaneIsometry K)
    (first second third : Plane.Point K) :
    Quadrea.Basic.quadrea (isometry first) (isometry second) (isometry third) =
      Quadrea.Basic.quadrea first second third := by
  unfold Quadrea.Basic.quadrea
  rw [isometry.preservesQuadrance, isometry.preservesQuadrance,
    isometry.preservesQuadrance]

/-- Theorem 91 (Isometries preserve collinearity), by the source's Quadrea argument. The characteristic-two exclusion is
mathematically necessary for this metric definition of isometry. -/
theorem preservesCollinearity [Nontrivial K] [DecidableEq K]
    (isometry : Isometry.Basic.PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (first second third : Plane.Point K) :
    Incidence.Collinear first second third ↔
      Incidence.Collinear (isometry first) (isometry second) (isometry third) := by
  have sourceIff :
      Quadrea.Basic.quadrea first second third = 0 ↔ Incidence.Collinear first second third := by
    exact Quadrea.Basic.triple_quad_formula first second third twoNonzero
  have imageIff :
      Quadrea.Basic.quadrea (isometry first) (isometry second) (isometry third) = 0 ↔
        Incidence.Collinear (isometry first) (isometry second) (isometry third) := by
    exact Quadrea.Basic.triple_quad_formula
      (isometry first) (isometry second) (isometry third) twoNonzero
  constructor
  · intro collinear
    apply imageIff.1
    rw [isometry.preservesQuadrea]
    exact sourceIff.2 collinear
  · intro collinear
    apply sourceIff.1
    rw [← isometry.preservesQuadrea first second third]
    exact imageIff.2 collinear

end

end Purelib.Geometry.Plane.Isometry.Basic.PlaneIsometry

end
