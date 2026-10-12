module
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
-- Exposed circle presentations retain these scalar-operation parents.
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order
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
public import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Geometry
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, §15.2: circles

Circle presentations retain the arbitrary nonzero common scale of the source's
six-coefficient conic notation.  Thus Theorem 100 proves genuine recovery of a
center and quadrance from a displayed conic rather than storing them as data.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- A conic presents the equation `Q(X,C) = k`, up to the displayed nonzero common coefficient `d`. -/
def IsCirclePresentation (conic : Conic K) (center :
  Plane.Point K)
    (circleQuadrance : K) : Prop :=
  conic.e = 0 ∧
    conic.d = conic.f ∧
    conic.d ≠ 0 ∧
    conic.a = -2 * conic.d * center.x ∧
    conic.b = -2 * conic.d * center.y ∧
    conic.c = conic.d *
      (center.x ^ 2 + center.y ^ 2 - circleQuadrance)

/-- A circle is a conic with an explicitly exhibited center and quadrance. -/
def IsCircle (conic : Conic K) : Prop :=
  ∃ center : Plane.Point K, ∃ circleQuadrance : K,
    conic.IsCirclePresentation center circleQuadrance

/-- The normalized coefficient record of `Q(X,C) = k`. -/
def circleConic [Nontrivial K] (center : Plane.Point K)
    (circleQuadrance : K) : Conic K where
  d := 1
  e := 0
  f := 1
  a := -2 * center.x
  b := -2 * center.y
  c := center.x ^ 2 + center.y ^ 2 - circleQuadrance
  quadratic_nonzero := Or.inl one_ne_zero

/-- The normalized construction has the claimed circle presentation. -/
theorem circleConic_isCirclePresentation [Nontrivial K] (center :
  Plane.Point K)
    (circleQuadrance : K) :
    (circleConic center circleQuadrance).IsCirclePresentation
      center circleQuadrance := by
  unfold circleConic IsCirclePresentation
  exact ⟨rfl, rfl, one_ne_zero, by ring1, by ring1, by ring1⟩

/-- Expanding a normalized circle gives `Q(X,C)-k`. -/
theorem circleConic_evaluate [Nontrivial K] (center point :
  Plane.Point K)
    (circleQuadrance : K) :
    (circleConic center circleQuadrance).evaluate point =
      Quadrance.quadrance point center - circleQuadrance := by
  unfold circleConic Conic.evaluate Quadrance.quadrance
  ring1

/-- Expanding any scaled circle presentation gives the same equation with a visible nonzero scale. -/
theorem evaluate_eq_scale_mul_quadrance_sub
    (conic : Conic K) (center point : Plane.Point K) (circleQuadrance : K)
    (presentation : conic.IsCirclePresentation center circleQuadrance) :
    conic.evaluate point =
      conic.d * (Quadrance.quadrance point center - circleQuadrance) := by
  rcases presentation with
    ⟨eZero, dEqualsF, _, aFormula, bFormula, cFormula⟩
  unfold Conic.evaluate Quadrance.quadrance
  rw [eZero, ← dEqualsF, aFormula, bFormula, cFormula]
  ring1

/-- A point lies on a presented circle exactly when its quadrance from the displayed center has the displayed value. -/
theorem contains_iff_quadrance_eq
    (conic : Conic K) (center point : Plane.Point K) (circleQuadrance : K)
    (presentation : conic.IsCirclePresentation center circleQuadrance) :
    conic.Contains point ↔ Quadrance.quadrance point center = circleQuadrance := by
  have dNonzero := presentation.2.2.1
  rw [Conic.Contains, evaluate_eq_scale_mul_quadrance_sub conic center point
    circleQuadrance presentation]
  constructor
  · intro scaledZero
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left dNonzero scaledZero
    calc
      Quadrance.quadrance point center =
          (Quadrance.quadrance point center - circleQuadrance) + circleQuadrance := by
            ring1
      _ = circleQuadrance := by rw [differenceZero]; ring1
  · intro equality
    rw [equality]
    ring1

/-- Theorem 100 (Circle uniqueness): two circle equations presenting the same displayed conic have the same center and
the same quadrance. -/
theorem circle_uniqueness (conic : Conic K) (twoNonzero : (2 :
  K) ≠ 0)
    {center otherCenter : Plane.Point K} {circleQuadrance otherQuadrance : K}
    (presentation :
      conic.IsCirclePresentation center circleQuadrance)
    (otherPresentation :
      conic.IsCirclePresentation otherCenter otherQuadrance) :
    center = otherCenter ∧ circleQuadrance = otherQuadrance := by
  have dNonzero := presentation.2.2.1
  have scaleNonzero : -2 * conic.d ≠ 0 :=
    ExplicitField.mul_ne_zero
      (Characteristic.Nonzero.negative_two_nonzero twoNonzero) dNonzero
  have xEqual : center.x = otherCenter.x := by
    apply ExplicitField.eq_of_mul_eq_mul_left scaleNonzero
    calc
      (-2 * conic.d) * center.x = conic.a :=
        presentation.2.2.2.1.symm
      _ = (-2 * conic.d) * otherCenter.x :=
        otherPresentation.2.2.2.1
  have yEqual : center.y = otherCenter.y := by
    apply ExplicitField.eq_of_mul_eq_mul_left scaleNonzero
    calc
      (-2 * conic.d) * center.y = conic.b :=
        presentation.2.2.2.2.1.symm
      _ = (-2 * conic.d) * otherCenter.y :=
        otherPresentation.2.2.2.2.1
  have centersEqual : center = otherCenter := Plane.Point.ext xEqual yEqual
  have scaledConstantsEqual :
      conic.d *
          (center.x ^ 2 + center.y ^ 2 - circleQuadrance) =
        conic.d *
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
    calc
      conic.d *
          (center.x ^ 2 + center.y ^ 2 - circleQuadrance) = conic.c :=
        presentation.2.2.2.2.2.symm
      _ = conic.d *
          (otherCenter.x ^ 2 + otherCenter.y ^ 2 - otherQuadrance) :=
        otherPresentation.2.2.2.2.2
      _ = conic.d *
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
        rw [← centersEqual]
  have constantsEqual :=
    ExplicitField.eq_of_mul_eq_mul_left dNonzero scaledConstantsEqual
  have quadrancesEqual : circleQuadrance = otherQuadrance := by
    calc
      circleQuadrance =
          center.x ^ 2 + center.y ^ 2 -
            (center.x ^ 2 + center.y ^ 2 - circleQuadrance) := by ring1
      _ = center.x ^ 2 + center.y ^ 2 -
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
        rw [constantsEqual]
      _ = otherQuadrance := by ring1
  exact ⟨centersEqual, quadrancesEqual⟩

/-- Theorem 100 packaged as unique existence from the definition of circle. -/
theorem circle_has_unique_presentation (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0) (isCircle : conic.IsCircle) :
    ∃ center : Plane.Point K, ∃ circleQuadrance : K,
      conic.IsCirclePresentation center circleQuadrance ∧
        ∀ otherCenter : Plane.Point K, ∀ otherQuadrance : K,
          conic.IsCirclePresentation otherCenter otherQuadrance →
            otherCenter = center ∧ otherQuadrance = circleQuadrance := by
  rcases isCircle with ⟨center, circleQuadrance, presentation⟩
  refine ⟨center, circleQuadrance, presentation, ?_⟩
  intro otherCenter otherQuadrance otherPresentation
  exact circle_uniqueness conic twoNonzero otherPresentation presentation

/-- Exercise 15.4: a conic is a circle exactly when `e=0` and its two square coefficients are equal and nonzero. The
reverse direction constructs the center and quadrance explicitly. -/
theorem exercise_15_4 (conic : Conic K) (twoNonzero : (2 : K)
  ≠ 0) :
    conic.IsCircle ↔
      conic.e = 0 ∧ conic.d = conic.f ∧ conic.d ≠ 0 := by
  constructor
  · rintro ⟨center, circleQuadrance, presentation⟩
    exact ⟨presentation.1, presentation.2.1, presentation.2.2.1⟩
  · rintro ⟨eZero, dEqualsF, dNonzero⟩
    have scaleNonzero : -2 * conic.d ≠ 0 :=
      ExplicitField.mul_ne_zero
        (Characteristic.Nonzero.negative_two_nonzero twoNonzero) dNonzero
    let center : Plane.Point K :=
      ⟨conic.a / (-2 * conic.d), conic.b / (-2 * conic.d)⟩
    let circleQuadrance : K :=
      center.x ^ 2 + center.y ^ 2 - conic.c / conic.d
    refine ⟨center, circleQuadrance, eZero, dEqualsF, dNonzero, ?_, ?_, ?_⟩
    · dsimp only [center]
      calc
        conic.a =
            (conic.a / (-2 * conic.d)) * (-2 * conic.d) := by
          exact (ExplicitField.div_mul_cancel conic.a scaleNonzero).symm
        _ = -2 * conic.d * (conic.a / (-2 * conic.d)) := by ring1
    · dsimp only [center]
      calc
        conic.b =
            (conic.b / (-2 * conic.d)) * (-2 * conic.d) := by
          exact (ExplicitField.div_mul_cancel conic.b scaleNonzero).symm
        _ = -2 * conic.d * (conic.b / (-2 * conic.d)) := by ring1
    · dsimp only [circleQuadrance]
      calc
        conic.c = (conic.c / conic.d) * conic.d := by
          exact (ExplicitField.div_mul_cancel conic.c dNonzero).symm
        _ = conic.d *
            (center.x ^ 2 + center.y ^ 2 -
              (center.x ^ 2 + center.y ^ 2 - conic.c / conic.d)) := by
                ring1
end

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, §16.2: subtended spreads

The Extended spread law supplies the fixed cleared ratio on a circle.  A
second finite determinant identity for the two radius vectors converts that
ratio into the source's `S₂(s) = 4s(1-s)` formula.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- A point on a circle of nonzero quadrance differs from its center.

The retained circle presentation identifies its radial quadrance with the nonzero circle quadrance. -/
public theorem point_ne_center_of_circle_quadrance_ne_zero
    (circle : Conic K) (center point : Plane.Point K) (circleQuadrance : K)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (pointOnCircle : circle.Contains point) : point ≠ center := by
  have radius : Quadrance.quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointOnCircle
  intro pointEqualsCenter
  apply quadranceNonzero
  calc
    circleQuadrance = Quadrance.quadrance point center := radius.symm
    _ = Quadrance.quadrance center center := by rw [pointEqualsCenter]
    _ = 0 := Quadrance.quadrance_self center

end

end Purelib.Curves.Plane.Conic

end
