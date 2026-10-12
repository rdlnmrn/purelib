module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Trigonometry.Spread.Triple

section
public section

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

namespace Surfaces.Ellipson.Sections.Coordinate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Coordinate-plane ellipse sections -/

/-- The quadratic equation of a section with the third coordinate fixed. -/
@[expose] def CoordinateCrossSection (fixed x y :
  K) : Prop :=
  x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
      2 * fixed * (x + y) + fixed ^ 2 = 0

/-- Fixing the third ellipson coordinate gives the displayed quadratic cross-section equation. -/
theorem fixed_third_cross_section (fixed x y : K)
  :
    Ellipson.Contains x y fixed ↔ CoordinateCrossSection fixed x
      y := by
  unfold Ellipson.Contains Ellipson.polynomial
    CoordinateCrossSection
  constructor
  · intro ellipsonZero
    calc
      x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 =
        -((x + y + fixed) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + fixed ^ 2) - 4 * x * y * fixed) := by
          ring1
      _ = 0 := by rw [ellipsonZero]; ring1
  · intro sectionZero
    calc
      (x + y + fixed) ^ 2 - 2 * (x ^ 2 + y ^ 2 + fixed ^ 2) -
          4 * x * y * fixed =
        -(x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2) := by ring1
      _ = 0 := by rw [sectionZero]; ring1

/-- The same equation describes sections in either other coordinate direction, by the ellipson's symmetry. -/
theorem all_coordinate_cross_sections (fixed
  first second : K) :
    (Ellipson.Contains fixed first second ↔
      CoordinateCrossSection fixed first second) ∧
      (Ellipson.Contains first fixed second ↔
        CoordinateCrossSection fixed first second) ∧
      (Ellipson.Contains first second fixed ↔
        CoordinateCrossSection fixed first second) := by
  constructor
  · exact (Ellipson.contains_permutations fixed first second).2.2.1.trans
      (fixed_third_cross_section fixed first second)
  constructor
  · exact (Ellipson.contains_permutations first fixed second).1.trans
      (fixed_third_cross_section fixed first second)
  · exact fixed_third_cross_section fixed first second

/-- Diagonalizing the coordinate section about `[1/2,1/2]` yields its denominator-free ellipse form. -/
theorem coordinate_cross_section_centered (fixed
  x y : K) :
    CoordinateCrossSection fixed x y ↔
      fixed * (x + y - 1) ^ 2 +
        (1 - fixed) * (x - y) ^ 2 = fixed * (1 - fixed) := by
  unfold CoordinateCrossSection
  constructor
  · intro sectionZero
    apply Group.eq_of_sub_eq_zero
    calc
      fixed * (x + y - 1) ^ 2 +
          (1 - fixed) * (x - y) ^ 2 - fixed * (1 - fixed) =
        x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 := by ring1
      _ = 0 := sectionZero
  · intro centered
    calc
      x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 =
        fixed * (x + y - 1) ^ 2 +
          (1 - fixed) * (x - y) ^ 2 - fixed * (1 - fixed) := by ring1
      _ = 0 := (by rewrite [centered]; exact sub_self _)

/-- At first coordinate zero, the section equation is the double root `(y - fixed)² = 0`. -/
theorem cross_section_x_zero (fixed y : K) :
    CoordinateCrossSection fixed 0 y ↔ (y - fixed) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (y - fixed) ^ 2 =
          0 ^ 2 + y ^ 2 + (4 * fixed - 2) * 0 * y -
            2 * fixed * (0 + y) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      0 ^ 2 + y ^ 2 + (4 * fixed - 2) * 0 * y -
          2 * fixed * (0 + y) + fixed ^ 2 = (y - fixed) ^ 2 := by ring1
      _ = 0 := equation

/-- At first coordinate one, the section equation is the double root `(y - (1 - fixed))² = 0`. -/
theorem cross_section_x_one (fixed y : K) :
    CoordinateCrossSection fixed 1 y ↔ (y - (1 - fixed)) ^ 2 = 0
      := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (y - (1 - fixed)) ^ 2 =
          1 ^ 2 + y ^ 2 + (4 * fixed - 2) * 1 * y -
            2 * fixed * (1 + y) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      1 ^ 2 + y ^ 2 + (4 * fixed - 2) * 1 * y -
          2 * fixed * (1 + y) + fixed ^ 2 =
        (y - (1 - fixed)) ^ 2 := by ring1
      _ = 0 := equation

/-- At second coordinate zero, the section equation is the double root `(x - fixed)² = 0`. -/
theorem cross_section_y_zero (fixed x : K) :
    CoordinateCrossSection fixed x 0 ↔ (x - fixed) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (x - fixed) ^ 2 =
          x ^ 2 + 0 ^ 2 + (4 * fixed - 2) * x * 0 -
            2 * fixed * (x + 0) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      x ^ 2 + 0 ^ 2 + (4 * fixed - 2) * x * 0 -
          2 * fixed * (x + 0) + fixed ^ 2 = (x - fixed) ^ 2 := by ring1
      _ = 0 := equation

/-- At second coordinate one, the section equation is the double root `(x - (1 - fixed))² = 0`. -/
theorem cross_section_y_one (fixed x : K) :
    CoordinateCrossSection fixed x 1 ↔ (x - (1 - fixed)) ^ 2 = 0
      := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (x - (1 - fixed)) ^ 2 =
          x ^ 2 + 1 ^ 2 + (4 * fixed - 2) * x * 1 -
            2 * fixed * (x + 1) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      x ^ 2 + 1 ^ 2 + (4 * fixed - 2) * x * 1 -
          2 * fixed * (x + 1) + fixed ^ 2 =
        (x - (1 - fixed)) ^ 2 := by ring1
      _ = 0 := equation

/-- The four double boundary roots are the exact algebraic form of tangency to the unit square. -/
theorem coordinate_cross_section_tangencies
  (fixed : K) :
    CoordinateCrossSection fixed 0 fixed ∧
      CoordinateCrossSection fixed 1 (1 - fixed) ∧
      CoordinateCrossSection fixed fixed 0 ∧
      CoordinateCrossSection fixed (1 - fixed) 1 := by
  constructor
  · exact (cross_section_x_zero fixed fixed).mpr (by ring1)
  constructor
  · exact (cross_section_x_one fixed (1 - fixed)).mpr (by ring1)
  constructor
  · exact (cross_section_y_zero fixed fixed).mpr (by ring1)
  · exact (cross_section_y_one fixed (1 - fixed)).mpr (by ring1)
end Surfaces.Ellipson.Sections.Coordinate
end Purelib.Geometry

end

end
