module
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The unit circle `x²+y²=1`. -/
def unitCircle [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 1
  a := 0
  b := 0
  c := -1
  quadratic_nonzero := Or.inl one_ne_zero

/-- Rational parametrization formula for a unit-circle point.

The coordinates use denominator `1 + parameter²`; membership requires its nonvanishing and is proved separately. -/
def unitCirclePoint (parameter : K) : Plane.Point K :=
  ⟨(1 - parameter ^ 2) / (1 + parameter ^ 2),
    (2 * parameter) / (1 + parameter ^ 2)⟩

/-- The one unit-circle point omitted by the rational parametrization. -/
def unitCircleExcludedPoint : Plane.Point K := ⟨-1, 0⟩

/-- The unit circle evaluates to its printed equation. -/
theorem unitCircle_evaluate [Nontrivial K] (point :
  Plane.Point K) :
    Curves.Plane.Conic.unitCircle.evaluate point = point.x ^ 2 + point.y ^ 2 - 1 := by
  unfold unitCircle Conic.evaluate
  ring1

/-- Incidence with the unit circle is the equation `x²+y²=1`. -/
theorem unitCircle_contains_iff [Nontrivial K] (point :
  Plane.Point K) :
    Curves.Plane.Conic.unitCircle.Contains point ↔ point.x ^ 2 + point.y ^ 2 - 1 = 0 := by
  unfold Conic.Contains
  rw [unitCircle_evaluate]

/-- The coefficient conic has the stated center and unit quadrance. -/
theorem unitCircle_isCirclePresentation [Nontrivial K] :
    Curves.Plane.Conic.unitCircle.IsCirclePresentation Conic.unitCircleCenter (1 : K) := by
  change (0 : K) = 0 ∧ (1 : K) = 1 ∧ (1 : K) ≠ 0 ∧
    0 = -2 * 1 * 0 ∧ 0 = -2 * 1 * 0 ∧
      -1 = 1 * (0 ^ 2 + 0 ^ 2 - 1)
  exact ⟨rfl, rfl, one_ne_zero, by ring1, by ring1, by ring1⟩

/-- The four unit-circle points displayed immediately before Theorem 107. -/
theorem unitCircle_four_points [Nontrivial K] :
    Curves.Plane.Conic.unitCircle.Contains (⟨1, 0⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.unitCircle.Contains (⟨-1, 0⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.unitCircle.Contains (⟨0, 1⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.unitCircle.Contains (⟨0, -1⟩ : Plane.Point K) := by
  repeat' apply And.intro
  all_goals
    apply (unitCircle_contains_iff _).2
    dsimp only
    ring1

end

end Purelib.Curves.Plane.Conic

end
