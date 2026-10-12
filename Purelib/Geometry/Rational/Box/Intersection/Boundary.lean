module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Boundary

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Intersection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
meta import Mathlib.Tactic.Linter.Lint

/-!
# Boundary points of retained coordinate intersections

A supplied common subbox keeps the intersection endpoints ordered. Each of its
four sides is one original side, so every boundary point belongs to at least
one input boundary, including coincident sides and corners.
-/

public section

namespace Purelib.Geometry.Rational.Box.Intersection.Boundary

open Purelib
open Purelib.Geometry.Rational.Box
open Purelib.Data.Rat

section Boxes.Box

variable {first second common : Geometry.Rational.Box}
  {inFirst : common.Refines first} {inSecond : common.Refines second}

/-- Every intersection boundary point lies on an original input boundary.

The selected endpoint in each coordinate identifies one input side. The
intersection's two refinement witnesses retain membership in that same box. -/
theorem intersection_boundary {point : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary (intersection first second common inFirst inSecond) point)
      :
    Boundary.OnBoxBoundary first point ∨ Boundary.OnBoxBoundary second point := by
  have firstInside := (intersection_refines_first (inFirst := inFirst) (inSecond :=
    inSecond)).contains boundary.1
  have secondInside := (intersection_refines_second (inFirst := inFirst) (inSecond :=
    inSecond)).contains boundary.1
  rcases boundary.2 with left | right | bottom | top
  · by_cases order : first.xLower ≤ second.xLower
    · change point.re = max first.xLower second.xLower at left
      rw [Fraction.Order.Basic.max_eq_right order] at left
      exact Or.inr ⟨secondInside, Or.inl left⟩
    · change point.re = max first.xLower second.xLower at left
      rw [Fraction.Order.Basic.max_eq_left
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le] at left
      exact Or.inl ⟨firstInside, Or.inl left⟩
  · by_cases order : first.xUpper ≤ second.xUpper
    · change point.re = (if first.xUpper ≤ second.xUpper then first.xUpper else second.xUpper) at right
      rw [if_pos order] at right
      exact Or.inl ⟨firstInside, Or.inr (Or.inl right)⟩
    · change point.re = (if first.xUpper ≤ second.xUpper then first.xUpper else second.xUpper) at right
      rw [if_neg order] at right
      exact Or.inr ⟨secondInside, Or.inr (Or.inl right)⟩
  · by_cases order : first.yLower ≤ second.yLower
    · change point.im = max first.yLower second.yLower at bottom
      rw [Fraction.Order.Basic.max_eq_right order] at bottom
      exact Or.inr ⟨secondInside, Or.inr (Or.inr (Or.inl bottom))⟩
    · change point.im = max first.yLower second.yLower at bottom
      rw [Fraction.Order.Basic.max_eq_left
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le] at bottom
      exact Or.inl ⟨firstInside, Or.inr (Or.inr (Or.inl bottom))⟩
  · by_cases order : first.yUpper ≤ second.yUpper
    · change point.im = (if first.yUpper ≤ second.yUpper then first.yUpper else second.yUpper) at top
      rw [if_pos order] at top
      exact Or.inl ⟨firstInside, Or.inr (Or.inr (Or.inr top))⟩
    · change point.im = (if first.yUpper ≤ second.yUpper then first.yUpper else second.yUpper) at top
      rw [if_neg order] at top
      exact Or.inr ⟨secondInside, Or.inr (Or.inr (Or.inr top))⟩

end Boxes.Box
end Purelib.Geometry.Rational.Box.Intersection.Boundary
