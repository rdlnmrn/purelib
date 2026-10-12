module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

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

namespace Surfaces.Ellipson.Sections.PlaneTwo

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## The oblique section and rational polar conversion -/

/-- The direct two-coordinate equation obtained by substituting `z=2-x-y` into the ellipson. -/
def PlaneTwoCrossSection (x y : K) : Prop :=
  4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
      4 * x * y * (2 - x - y) = 0

/-- Substituting `z = 2 - x - y` gives the plane-two section equation of the ellipson. -/
theorem plane_two_cross_section (x y : K) :
    Ellipson.Contains x y (2 - x - y) ↔ PlaneTwoCrossSection x y
      := by
  unfold Ellipson.Contains Ellipson.polynomial
    PlaneTwoCrossSection
  constructor <;> intro equation
  · calc
      4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) =
        (x + y + (2 - x - y)) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) := by ring1
      _ = 0 := equation
  · calc
      (x + y + (2 - x - y)) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) =
        4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) := by ring1
      _ = 0 := equation
end Surfaces.Ellipson.Sections.PlaneTwo
end Purelib.Geometry

end
