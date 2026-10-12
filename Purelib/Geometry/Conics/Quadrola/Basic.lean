module

import Purelib.Algebra.Field.Characteristic.Nonzero
public import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Init.Prelude
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

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry.Conics.Quadrola

section

variable {K : Type*} [ExplicitField K]

/-- The defining equation (15.4). -/
def evaluate (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) (point : Plane.Point K) : K :=
  QuadTriple.Basic.archimedesFunction (Quadrance.quadrance point firstFocus)
    (Quadrance.quadrance point secondFocus) associatedQuadrance

/-- Membership in the quadrola defined by two foci and an associated quadrance.

The Archimedes polynomial of the two focal quadrances and the associated quadrance must vanish. -/
def Contains (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) (point : Plane.Point K) : Prop :=
  evaluate firstFocus secondFocus associatedQuadrance point = 0

/-- Nondegeneracy conditions for a quadrola presentation.

The foci are distinct, their quadrance and the associated quadrance are nonzero, and these quadrances differ. -/
structure Presentation (firstFocus secondFocus :
  Plane.Point K)
    (associatedQuadrance : K) : Prop where
  /-- The two focal points are distinct. -/ fociDistinct : firstFocus ≠ secondFocus
  /-- The associated quadrance is nonzero. -/ associatedNonzero : associatedQuadrance ≠ 0
  /-- The focal separation has nonzero quadrance. -/ focusQuadranceNonzero : Quadrance.quadrance firstFocus secondFocus
    ≠ 0
  /-- The focal quadrance differs from the associated quadrance. -/ focusQuadranceDifferent :
    Quadrance.quadrance firstFocus secondFocus ≠ associatedQuadrance

/-- The `x²` coefficient after expansion of the quadrola equation. -/
def conicD (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) : K :=
  4 * (associatedQuadrance - (secondFocus.x - firstFocus.x) ^ 2)

/-- The `xy` coefficient after expansion. -/
def conicE (firstFocus secondFocus : Plane.Point K) :
  K :=
  -8 * (secondFocus.x - firstFocus.x) *
    (secondFocus.y - firstFocus.y)

/-- The `y²` coefficient after expansion. -/
def conicF (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) : K :=
  4 * (associatedQuadrance - (secondFocus.y - firstFocus.y) ^ 2)

/-- Coefficient of `x` in the expanded quadrola equation. -/
def conicA (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) : K :=
  -4 * ((secondFocus.x - firstFocus.x) *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 -
        secondFocus.x ^ 2 - secondFocus.y ^ 2) +
    associatedQuadrance * (firstFocus.x + secondFocus.x))

/-- Coefficient of `y` in the expanded quadrola equation. -/
def conicB (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) : K :=
  -4 * ((secondFocus.y - firstFocus.y) *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 -
        secondFocus.x ^ 2 - secondFocus.y ^ 2) +
    associatedQuadrance * (firstFocus.y + secondFocus.y))

/-- Constant coefficient in the expanded quadrola equation. -/
def conicC (firstFocus secondFocus : Plane.Point K)
    (associatedQuadrance : K) : K :=
  -(firstFocus.x ^ 2 + firstFocus.y ^ 2 -
      secondFocus.x ^ 2 - secondFocus.y ^ 2) ^ 2 +
    2 * associatedQuadrance *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 +
        secondFocus.x ^ 2 + secondFocus.y ^ 2) -
    associatedQuadrance ^ 2

end
end Purelib.Geometry.Conics.Quadrola

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Conics.Quadrola

/-- The expanded quadrola has a nonzero quadratic coefficient.

Nonzero associated quadrance and nonzero eight rule out simultaneous vanishing of all three quadratic coefficients. -/
private theorem conic_quadratic_nonzero
  [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) :
    conicD firstFocus secondFocus associatedQuadrance ≠ 0 ∨
      conicE firstFocus secondFocus ≠ 0 ∨
      conicF firstFocus secondFocus associatedQuadrance ≠ 0 := by
  by_cases dZero : conicD firstFocus secondFocus associatedQuadrance = 0
  · by_cases eZero : conicE firstFocus secondFocus = 0
    · right
      right
      intro fZero
      let deltaX := secondFocus.x - firstFocus.x
      let deltaY := secondFocus.y - firstFocus.y
      have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero_of_eight_ne_zero eightNonzero
      have firstDifferenceZero :
          associatedQuadrance - deltaX ^ 2 = 0 := by
        apply ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero
        simpa only [conicD, deltaX] using dZero
      have secondDifferenceZero :
          associatedQuadrance - deltaY ^ 2 = 0 := by
        apply ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero
        simpa only [conicF, deltaY] using fZero
      have deltaProductZero : deltaX * deltaY = 0 := by
        apply ExplicitField.eq_zero_of_mul_eq_zero_left eightNonzero
        calc
          (8 : K) * (deltaX * deltaY) =
              -(conicE firstFocus secondFocus) := by
            unfold conicE deltaX deltaY
            ring1
          _ = 0 := by rw [eZero]; ring1
      have deltaXNonzero : deltaX ≠ 0 := by
        intro deltaXZero
        apply associatedNonzero
        calc
          associatedQuadrance =
              (associatedQuadrance - deltaX ^ 2) + deltaX ^ 2 := by ring1
          _ = 0 := by rw [firstDifferenceZero, deltaXZero]; ring1
      have deltaYZero :=
        ExplicitField.eq_zero_of_mul_eq_zero_left deltaXNonzero deltaProductZero
      apply associatedNonzero
      calc
        associatedQuadrance =
            (associatedQuadrance - deltaY ^ 2) + deltaY ^ 2 := by ring1
        _ = 0 := by rw [secondDifferenceZero, deltaYZero]; ring1
    · exact Or.inr (Or.inl eZero)
  · exact Or.inl dZero
end Purelib.Geometry.Conics.Quadrola
end

namespace Purelib.Geometry.Conics.Quadrola

section

variable {K : Type*} [ExplicitField K]

/-- Exercise 15.11's explicit conic obtained from the quadrola equation. -/
def conic [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) : Conic K where
  d := conicD firstFocus secondFocus associatedQuadrance
  e := conicE firstFocus secondFocus
  f := conicF firstFocus secondFocus associatedQuadrance
  a := conicA firstFocus secondFocus associatedQuadrance
  b := conicB firstFocus secondFocus associatedQuadrance
  c := conicC firstFocus secondFocus associatedQuadrance
  quadratic_nonzero := by
    by_cases dZero : conicD firstFocus secondFocus associatedQuadrance = 0
    · by_cases eZero : conicE firstFocus secondFocus = 0
      · right
        right
        intro fZero
        let deltaX := secondFocus.x - firstFocus.x
        let deltaY := secondFocus.y - firstFocus.y
        have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero_of_eight_ne_zero eightNonzero
        have firstDifferenceZero :
            associatedQuadrance - deltaX ^ 2 = 0 := by
          apply ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero
          simpa only [conicD, deltaX] using dZero
        have secondDifferenceZero :
            associatedQuadrance - deltaY ^ 2 = 0 := by
          apply ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero
          simpa only [conicF, deltaY] using fZero
        have deltaProductZero : deltaX * deltaY = 0 := by
          apply ExplicitField.eq_zero_of_mul_eq_zero_left eightNonzero
          calc
            (8 : K) * (deltaX * deltaY) =
                -(conicE firstFocus secondFocus) := by
              unfold conicE deltaX deltaY
              ring1
            _ = 0 := by rw [eZero]; ring1
        have deltaXNonzero : deltaX ≠ 0 := by
          intro deltaXZero
          apply associatedNonzero
          calc
            associatedQuadrance =
                (associatedQuadrance - deltaX ^ 2) + deltaX ^ 2 := by ring1
            _ = 0 := by rw [firstDifferenceZero, deltaXZero]; ring1
        have deltaYZero :=
          ExplicitField.eq_zero_of_mul_eq_zero_left deltaXNonzero deltaProductZero
        apply associatedNonzero
        calc
          associatedQuadrance =
              (associatedQuadrance - deltaY ^ 2) + deltaY ^ 2 := by ring1
          _ = 0 := by rw [secondDifferenceZero, deltaYZero]; ring1
      · exact Or.inr (Or.inl eZero)
    · exact Or.inl dZero

/-- Exercise 15.11: the six-coefficient conic evaluates to the defining Archimedes polynomial. -/
theorem conic_evaluate [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Plane.Point K) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).evaluate point =
        evaluate firstFocus secondFocus associatedQuadrance point := by
  unfold conic Conic.evaluate evaluate
    conicD conicE conicF
    conicA conicB
    conicC Quadrance.quadrance QuadTriple.Basic.archimedesFunction
  ring1
end

end Purelib.Geometry.Conics.Quadrola

end
