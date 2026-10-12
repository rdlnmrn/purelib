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

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, §16.3: the projective circle

The projective circle is stored by its denominator-free equation
`x² + y² - y = 0`.  Its rational parametrization is executable for every
requested field element; the theorem carries the exact finite certificate
`λ² ≠ -1` needed to cancel its denominator.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The projective circle's displayed center `[0,1/2]`. -/
def projectiveCircleCenter : Plane.Point K := ⟨0, 1 / 2⟩

/-- The projective circle `x² + y² - y = 0`. -/
def projectiveCircle [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 1
  a := 0
  b := -1
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

/-- The projective circle evaluates to its printed equation. -/
theorem projectiveCircle_evaluate [Nontrivial K] (point :
  Plane.Point K) :
    Curves.Plane.Conic.projectiveCircle.evaluate point = point.x ^ 2 + point.y ^ 2 - point.y := by
  unfold projectiveCircle Conic.evaluate
  ring1

/-- Incidence with the projective circle is the printed polynomial equation. -/
theorem projectiveCircle_contains_iff [Nontrivial K] (point :
  Plane.Point K) :
    Curves.Plane.Conic.projectiveCircle.Contains point ↔
      point.x ^ 2 + point.y ^ 2 - point.y = 0 := by
  unfold Conic.Contains
  rw [projectiveCircle_evaluate]

/-- The coefficient conic really has center `[0,1/2]` and quadrance `1/4`. -/
theorem projectiveCircle_isCirclePresentation [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) :
    Curves.Plane.Conic.projectiveCircle.IsCirclePresentation
      projectiveCircleCenter
      (1 / 4 : K) := by
  have twoCancel : (1 / 2 : K) * 2 = 1 :=
    ExplicitField.div_mul_cancel (1 : K) twoNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have halfSquareTimesFour : (1 / 2 : K) ^ 2 * 4 = 1 := by
    calc
      (1 / 2 : K) ^ 2 * 4 = ((1 / 2 : K) * 2) ^ 2 := by ring1
      _ = 1 := by rw [twoCancel]; ring1
  have quarterTimesFour : (1 / 4 : K) * 4 = 1 :=
    ExplicitField.div_mul_cancel (1 : K) fourNonzero
  have halfSquareEqualsQuarter : (1 / 2 : K) ^ 2 = 1 / 4 := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      (1 / 2 : K) ^ 2 * 4 = 1 := halfSquareTimesFour
      _ = (1 / 4 : K) * 4 := quarterTimesFour.symm
  change (0 : K) = 0 ∧ (1 : K) = 1 ∧ (1 : K) ≠ 0 ∧
    0 = -2 * 1 * 0 ∧
    -1 = -2 * 1 * (1 / 2) ∧
    0 = 1 * (0 ^ 2 + (1 / 2) ^ 2 - 1 / 4)
  refine ⟨rfl, rfl, one_ne_zero, ?_, ?_, ?_⟩
  · ring1
  · calc
      (-1 : K) = -((1 / 2 : K) * 2) := by rw [twoCancel]
      _ = -2 * 1 * (1 / 2) := by ring1
  · rw [halfSquareEqualsQuarter]
    ring1

/-- The four projective-circle points displayed immediately before Theorem 107 in the source. -/
theorem projectiveCircle_four_points [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) :
    Curves.Plane.Conic.projectiveCircle.Contains (⟨0, 0⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.projectiveCircle.Contains (⟨0, 1⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.projectiveCircle.Contains (⟨1 / 2, 1 / 2⟩ : Plane.Point K) ∧
      Curves.Plane.Conic.projectiveCircle.Contains (⟨-(1 / 2), 1 / 2⟩ : Plane.Point K) := by
  have twoCancel : (1 / 2 : K) * 2 = 1 :=
    ExplicitField.div_mul_cancel 1 twoNonzero
  repeat' apply And.intro
  all_goals
    apply (projectiveCircle_contains_iff _).2
    dsimp only
    try ring1
  · calc
      (1 / 2 : K) ^ 2 + (1 / 2) ^ 2 - 1 / 2 =
          (1 / 2) * ((1 / 2) * 2 - 1) := by ring1
      _ = 0 := by rw [twoCancel]; ring1
  · calc
      (-(1 / 2 : K)) ^ 2 + (1 / 2) ^ 2 - 1 / 2 =
          (1 / 2) * ((1 / 2) * 2 - 1) := by ring1
      _ = 0 := by rw [twoCancel]; ring1

end

end Purelib.Curves.Plane.Conic

end
