module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Curves.Plane.Conic.Center
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.QuadraticPart
public import Purelib.Geometry.Conics.Quadrola.Basic
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Conics.Quadrola
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Point.Affine
open Purelib.Geometry.Trigonometry.QuadTriple.Basic

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Conics.Quadrola.Center

/-- The center discriminant of the canonical quadrola coefficients. -/
theorem conic_centerDiscriminant [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).centerDiscriminant =
        64 * associatedQuadrance *
          (Quadrance.quadrance firstFocus secondFocus - associatedQuadrance) := by
  unfold Curves.Plane.Conic.centerDiscriminant Quadrola.conic Quadrola.conicD Quadrola.conicE
    Quadrola.conicF Quadrance.quadrance
  ring1

/-- The canonical equation evaluated at the midpoint of its foci. -/
theorem conic_evaluate_midpoint [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).evaluate (Affine.midpoint firstFocus secondFocus) =
        associatedQuadrance *
          (Quadrance.quadrance firstFocus secondFocus - associatedQuadrance) := by
  have equalMidpointQuadrances :=
    Quadrance.midpoint_equal_quadrance firstFocus secondFocus twoNonzero
  have midpointValue := Quadrance.midpoint_quadrance firstFocus secondFocus twoNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 4 fourNonzero
  calc
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero).evaluate (Affine.midpoint firstFocus secondFocus) =
      Quadrola.evaluate firstFocus secondFocus associatedQuadrance
        (Affine.midpoint firstFocus secondFocus) :=
      Quadrola.conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (Affine.midpoint firstFocus secondFocus)
    _ = -(Quadrance.quadrance (Affine.midpoint firstFocus secondFocus) firstFocus -
            Quadrance.quadrance (Affine.midpoint firstFocus secondFocus) secondFocus) ^ 2 +
          2 * associatedQuadrance *
            (Quadrance.quadrance (Affine.midpoint firstFocus secondFocus) firstFocus +
              Quadrance.quadrance (Affine.midpoint firstFocus secondFocus) secondFocus) -
          associatedQuadrance ^ 2 := by
      unfold Quadrola.evaluate
      rw [Quadrola.archimedes_difference_identity]
    _ = 4 * associatedQuadrance *
          Quadrance.quadrance (Affine.midpoint firstFocus secondFocus) firstFocus -
          associatedQuadrance ^ 2 := by
      rw [equalMidpointQuadrances]
      ring1
    _ = 4 * associatedQuadrance *
          (Quadrance.quadrance firstFocus secondFocus * (4 : K)⁻¹) -
          associatedQuadrance ^ 2 := by
      rw [midpointValue, Algebra.Field.ExplicitField.div_eq_mul_inv]
    _ = associatedQuadrance *
          (Quadrance.quadrance firstFocus secondFocus - associatedQuadrance) := by
      calc
        4 * associatedQuadrance *
              (Quadrance.quadrance firstFocus secondFocus * (4 : K)⁻¹) -
              associatedQuadrance ^ 2 =
            associatedQuadrance * Quadrance.quadrance firstFocus secondFocus *
                (4 * (4 : K)⁻¹) - associatedQuadrance ^ 2 := by ring1
        _ = associatedQuadrance *
            (Quadrance.quadrance firstFocus secondFocus - associatedQuadrance) := by
          rw [fourCancel]
          ring1

/-- A valid quadrola presentation has nonzero center discriminant.

The discriminant factors as sixty-four times the associated quadrance and the difference between focal and associated
quadrances. -/
theorem conic_discriminant_nonzero [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (presentation : Quadrola.Presentation firstFocus secondFocus associatedQuadrance)
    (eightNonzero : (8 : K) ≠ 0) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance
      presentation.associatedNonzero eightNonzero).centerDiscriminant ≠ 0 := by
  have sixtyFourNonzero : (64 : K) ≠ 0 := by
    have sixtyFourAsProduct : (64 : K) = 8 * 8 := by ring1
    rw [sixtyFourAsProduct]
    exact Algebra.Field.ExplicitField.mul_ne_zero eightNonzero eightNonzero
  have differenceNonzero :
      Quadrance.quadrance firstFocus secondFocus - associatedQuadrance ≠ 0 := by
    intro differenceZero
    apply presentation.focusQuadranceDifferent
    calc
      Quadrance.quadrance firstFocus secondFocus =
          (Quadrance.quadrance firstFocus secondFocus - associatedQuadrance) +
            associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1
  rw [Purelib.Geometry.Conics.Quadrola.Center.conic_centerDiscriminant]
  exact Algebra.Field.ExplicitField.mul_ne_zero
    (Algebra.Field.ExplicitField.mul_ne_zero sixtyFourNonzero
      presentation.associatedNonzero) differenceNonzero

end Purelib.Geometry.Conics.Quadrola.Center

namespace Purelib.Geometry.Conics.Quadrola.Center

/-- The midpoint of the two foci is a center of the canonical quadrola conic.

The coefficient identity uses the nonzero constants required for construction and midpoint division, without additional
focal nondegeneracy assumptions. -/
public theorem conic_midpoint_isCenter [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsCenter (Affine.midpoint firstFocus secondFocus) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have midpointX :
      2 * (Affine.midpoint firstFocus secondFocus).x =
        firstFocus.x + secondFocus.x := by
    change 2 * ((firstFocus.x + secondFocus.x) / 2) =
      firstFocus.x + secondFocus.x
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * ((firstFocus.x + secondFocus.x) * (2 : K)⁻¹) =
          (firstFocus.x + secondFocus.x) * (2 * (2 : K)⁻¹) := by
            ring1
      _ = firstFocus.x + secondFocus.x := by rw [twoCancel]; ring1
  have midpointY :
      2 * (Affine.midpoint firstFocus secondFocus).y =
        firstFocus.y + secondFocus.y := by
    change 2 * ((firstFocus.y + secondFocus.y) / 2) =
      firstFocus.y + secondFocus.y
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * ((firstFocus.y + secondFocus.y) * (2 : K)⁻¹) =
          (firstFocus.y + secondFocus.y) * (2 * (2 : K)⁻¹) := by
            ring1
      _ = firstFocus.y + secondFocus.y := by rw [twoCancel]; ring1
  constructor
  · change
      2 * Quadrola.conicD firstFocus secondFocus associatedQuadrance *
            (Affine.midpoint firstFocus secondFocus).x +
          Quadrola.conicE firstFocus secondFocus *
            (Affine.midpoint firstFocus secondFocus).y +
          Quadrola.conicA firstFocus secondFocus associatedQuadrance = 0
    calc
      2 * Quadrola.conicD firstFocus secondFocus associatedQuadrance *
              (Affine.midpoint firstFocus secondFocus).x +
            Quadrola.conicE firstFocus secondFocus *
              (Affine.midpoint firstFocus secondFocus).y +
            Quadrola.conicA firstFocus secondFocus associatedQuadrance =
          Quadrola.conicD firstFocus secondFocus associatedQuadrance *
              (2 * (Affine.midpoint firstFocus secondFocus).x) -
            4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (2 * (Affine.midpoint firstFocus secondFocus).y) +
            Quadrola.conicA firstFocus secondFocus associatedQuadrance := by
              unfold Quadrola.conicE
              ring1
      _ = Quadrola.conicD firstFocus secondFocus associatedQuadrance *
              (firstFocus.x + secondFocus.x) -
            4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (firstFocus.y + secondFocus.y) +
            Quadrola.conicA firstFocus secondFocus associatedQuadrance := by
              rw [midpointX, midpointY]
      _ = 0 := by unfold Quadrola.conicD Quadrola.conicA; ring1
  · change
      Quadrola.conicE firstFocus secondFocus *
            (Affine.midpoint firstFocus secondFocus).x +
          2 * Quadrola.conicF firstFocus secondFocus associatedQuadrance *
            (Affine.midpoint firstFocus secondFocus).y +
          Quadrola.conicB firstFocus secondFocus associatedQuadrance = 0
    calc
      Quadrola.conicE firstFocus secondFocus *
              (Affine.midpoint firstFocus secondFocus).x +
            2 * Quadrola.conicF firstFocus secondFocus associatedQuadrance *
              (Affine.midpoint firstFocus secondFocus).y +
            Quadrola.conicB firstFocus secondFocus associatedQuadrance =
          -4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (2 * (Affine.midpoint firstFocus secondFocus).x) +
            Quadrola.conicF firstFocus secondFocus associatedQuadrance *
              (2 * (Affine.midpoint firstFocus secondFocus).y) +
            Quadrola.conicB firstFocus secondFocus associatedQuadrance := by
              unfold Quadrola.conicE
              ring1
      _ = -4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (firstFocus.x + secondFocus.x) +
            Quadrola.conicF firstFocus secondFocus associatedQuadrance *
              (firstFocus.y + secondFocus.y) +
            Quadrola.conicB firstFocus secondFocus associatedQuadrance := by
              rw [midpointX, midpointY]
      _ = 0 := by unfold Quadrola.conicF Quadrola.conicB; ring1

end Purelib.Geometry.Conics.Quadrola.Center

namespace Purelib.Geometry.Conics.Quadrola.Center

/-- Exercise 15.12: every quadrola conic is centered. The midpoint of its two displayed foci is an explicit center. No
nondegeneracy clause beyond the one needed to construct the conic is used by this coefficient identity. -/
theorem exercise_15_12 [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsCenter (Affine.midpoint firstFocus secondFocus) := by
  exact Purelib.Geometry.Conics.Quadrola.Center.conic_midpoint_isCenter firstFocus secondFocus
    associatedQuadrance
    associatedNonzero eightNonzero twoNonzero

end Purelib.Geometry.Conics.Quadrola.Center

end

end

end

end
