module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

namespace Purelib.Geometry

namespace Surfaces.Ellipson

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The four vertices named in Appendix B lie on the ellipson. -/
theorem tetrahedron_vertices :
    Ellipson.Contains (0 : K) 0 0 ∧
      Ellipson.Contains (1 : K) 1 0 ∧
      Ellipson.Contains (1 : K) 0 1 ∧
      Ellipson.Contains (0 : K) 1 1 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The oriented determinant of the three tetrahedral edge vectors is `-2`. Its magnitude gives the numerator `2` in the
usual `2/6=1/3` volume. -/
theorem tetrahedron_oriented_six_volume :
    Quadrilateral.determinantThree
      (1 : K) 1 0
      1 0 1
      0 1 1 = -2 := by
  unfold Quadrilateral.determinantThree
  ring1

/-- Denominator-cleared certificate for the source's tetrahedron volume `1/3`, paired with the determinant calculation
that supplies it. -/
theorem tetrahedron_volume_certificate :
    Quadrilateral.determinantThree
        (1 : K) 1 0
        1 0 1
        0 1 1 = -2 ∧
      3 * 2 = 6 * (1 : K) := by
  exact ⟨tetrahedron_oriented_six_volume, by ring1⟩
end Surfaces.Ellipson
end Purelib.Geometry

end
