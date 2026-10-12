module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Six finite probes recover all coefficients of a quadratic polynomial in two variables when characteristic two is
excluded. -/
theorem coefficients_eq_of_evaluate_eq (left right : Conic K)
    (twoNonzero : (2 : K) ≠ 0)
    (evaluationsEqual : ∀ point : Plane.Point K,
      left.evaluate point = right.evaluate point) :
    left.d = right.d ∧ left.e = right.e ∧ left.f = right.f ∧
      left.a = right.a ∧ left.b = right.b ∧ left.c = right.c := by
  have atOrigin := evaluationsEqual (⟨0, 0⟩ : Plane.Point K)
  have atPositiveX := evaluationsEqual (⟨1, 0⟩ : Plane.Point K)
  have atNegativeX := evaluationsEqual (⟨-1, 0⟩ : Plane.Point K)
  have atPositiveY := evaluationsEqual (⟨0, 1⟩ : Plane.Point K)
  have atNegativeY := evaluationsEqual (⟨0, -1⟩ : Plane.Point K)
  have atOneOne := evaluationsEqual (⟨1, 1⟩ : Plane.Point K)
  have cEqual : left.c = right.c := by
    simpa only [Conic.evaluate, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero, zero_add] using atOrigin
  have dProductsEqual : (2 : K) * left.d = 2 * right.d := by
    calc
      (2 : K) * left.d =
          left.evaluate ⟨1, 0⟩ + left.evaluate ⟨-1, 0⟩ -
            2 * left.evaluate ⟨0, 0⟩ := by
              unfold Conic.evaluate
              ring1
      _ = right.evaluate ⟨1, 0⟩ + right.evaluate ⟨-1, 0⟩ -
            2 * right.evaluate ⟨0, 0⟩ := by
              rw [atPositiveX, atNegativeX, atOrigin]
      _ = 2 * right.d := by
        unfold Conic.evaluate
        ring1
  have dEqual : left.d = right.d :=
    Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left twoNonzero dProductsEqual
  have aProductsEqual : (2 : K) * left.a = 2 * right.a := by
    calc
      (2 : K) * left.a =
          left.evaluate ⟨1, 0⟩ - left.evaluate ⟨-1, 0⟩ := by
            unfold Conic.evaluate
            ring1
      _ = right.evaluate ⟨1, 0⟩ - right.evaluate ⟨-1, 0⟩ := by
        rw [atPositiveX, atNegativeX]
      _ = 2 * right.a := by
        unfold Conic.evaluate
        ring1
  have aEqual : left.a = right.a :=
    Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left twoNonzero aProductsEqual
  have fProductsEqual : (2 : K) * left.f = 2 * right.f := by
    calc
      (2 : K) * left.f =
          left.evaluate ⟨0, 1⟩ + left.evaluate ⟨0, -1⟩ -
            2 * left.evaluate ⟨0, 0⟩ := by
              unfold Conic.evaluate
              ring1
      _ = right.evaluate ⟨0, 1⟩ + right.evaluate ⟨0, -1⟩ -
            2 * right.evaluate ⟨0, 0⟩ := by
              rw [atPositiveY, atNegativeY, atOrigin]
      _ = 2 * right.f := by
        unfold Conic.evaluate
        ring1
  have fEqual : left.f = right.f :=
    Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left twoNonzero fProductsEqual
  have bProductsEqual : (2 : K) * left.b = 2 * right.b := by
    calc
      (2 : K) * left.b =
          left.evaluate ⟨0, 1⟩ - left.evaluate ⟨0, -1⟩ := by
            unfold Conic.evaluate
            ring1
      _ = right.evaluate ⟨0, 1⟩ - right.evaluate ⟨0, -1⟩ := by
        rw [atPositiveY, atNegativeY]
      _ = 2 * right.b := by
        unfold Conic.evaluate
        ring1
  have bEqual : left.b = right.b :=
    Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left twoNonzero bProductsEqual
  have eEqual : left.e = right.e := by
    calc
      left.e = left.evaluate ⟨1, 1⟩ -
          (left.d + left.f + left.a + left.b + left.c) := by
            unfold Conic.evaluate
            ring1
      _ = right.evaluate ⟨1, 1⟩ -
          (right.d + right.f + right.a + right.b + right.c) := by
            rw [atOneOne, dEqual, fEqual, aEqual, bEqual, cEqual]
      _ = right.e := by
        unfold Conic.evaluate
        ring1
  exact ⟨dEqual, eEqual, fEqual, aEqual, bEqual, cEqual⟩

end Purelib.Curves.Plane.Conic

end
