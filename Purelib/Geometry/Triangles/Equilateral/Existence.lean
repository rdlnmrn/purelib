module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Triangles.Quadrance.Realization
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry.Triangles.Quadrance

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 further exercises

This module contains the equilateral centroid calculations, the unit-
quadrance existence criterion, and the corrected right-altitude formulas.
-/

namespace Purelib.Geometry.Triangles.Equilateral.Existence

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 10.5. A noncollinear equilateral triangle with unit common quadrance exists exactly when `3` is displayed
as a nonzero square. -/
theorem unit_quadrance_iff_nonzero_square_three [Nontrivial K]
  [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Realization.HasTriangleQuadrances (1 : K) 1 1 ↔ Squares.IsNonzeroSquare (3 : K) := by
  have criterion := Realization.triangle_quadrea (1 : K) 1 1 twoNonzero
  constructor
  · intro triangle
    have data := criterion.1 triangle
    rcases data.2.2.2.2 with ⟨root, rootNonzero, square⟩
    refine ⟨root, rootNonzero, ?_⟩
    calc
      (3 : K) = QuadTriple.Basic.archimedesFunction 1 1 1 := by
        unfold QuadTriple.Basic.archimedesFunction
        ring1
      _ = root ^ 2 := square
  · rintro ⟨root, rootNonzero, square⟩
    apply criterion.2
    refine ⟨Or.inl one_ne_zero,
      ⟨1, 0, by ring1⟩, ⟨1, 0, by ring1⟩,
      ⟨1, 0, by ring1⟩, root, rootNonzero, ?_⟩
    calc
      QuadTriple.Basic.archimedesFunction (1 : K) 1 1 = 3 := by
        unfold QuadTriple.Basic.archimedesFunction
        ring1
      _ = root ^ 2 := square
end Purelib.Geometry.Triangles.Equilateral.Existence

end
