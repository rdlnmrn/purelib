module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

public section

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
-- Retain the owned natural certificates and negation parent during numeral elaboration.
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The coordinate map `τ_{u,v}([x,y]) = [x+u,y+v]`. -/
@[expose] def translationPoint (u v : K) (point : Point K) : Point K :=
  ⟨point.x + u, point.y + v⟩
end Purelib.Geometry.Plane.Point.Affine

end

end

section
public section

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The coordinatewise weighted sum of two points.

The definition accepts arbitrary weights; incidence results separately require their sum to be one. -/
@[expose] def affineCombination (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) : Point K :=
  ⟨leftWeight * left.x + rightWeight * right.x,
    leftWeight * left.y + rightWeight * right.y⟩

/-- The coordinatewise weighted sum of three points.

The definition accepts arbitrary weights; barycentric results separately require their sum to be one. -/
@[expose] def affineCombinationThree
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) : Point K :=
  ⟨firstWeight * first.x + secondWeight * second.x +
      thirdWeight * third.x,
    firstWeight * first.y + secondWeight * second.y +
      thirdWeight * third.y⟩

/-- The first coordinate of the weighted three-point combination. -/
@[simp] theorem affineCombinationThree_x
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) :
    (Geometry.Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
      thirdWeight third).x =
      firstWeight * first.x + secondWeight * second.x +
        thirdWeight * third.x := rfl

/-- The second coordinate of the weighted three-point combination. -/
@[simp] theorem affineCombinationThree_y
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) :
    (Geometry.Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
      thirdWeight third).y =
      firstWeight * first.y + secondWeight * second.y +
        thirdWeight * third.y := rfl

/-- The first coordinate of the weighted two-point combination. -/
@[simp] theorem affineCombination_x (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) :
    (Geometry.Plane.Point.Affine.affineCombination leftWeight left rightWeight right).x =
      leftWeight * left.x + rightWeight * right.x := rfl

/-- The second coordinate of the weighted two-point combination. -/
@[simp] theorem affineCombination_y (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) :
    (Geometry.Plane.Point.Affine.affineCombination leftWeight left rightWeight right).y =
      leftWeight * left.y + rightWeight * right.y := rfl

/-- Midpoint of two displayed points. Theorems using its geometric meaning carry the source's explicit `2 ≠ 0`
hypothesis. -/
@[expose] def midpoint (first second : Point K) : Point K :=
  ⟨(first.x + second.x) / 2, (first.y + second.y) / 2⟩

section
/-- A two-level weighted combination equals the three-point combination when the outer first weight differs from one.

The inner weights divide the remaining two weights by the complement of the first weight. -/
private theorem nestedAffineCombination_eq_three
    (firstWeight secondWeight thirdWeight : K)
    (first second third : Point K)
    (firstNotOne : firstWeight ≠ 1) :
    Plane.Point.Affine.affineCombination firstWeight first (1 - firstWeight)
        (Plane.Point.Affine.affineCombination (secondWeight / (1 - firstWeight)) second
          (thirdWeight / (1 - firstWeight)) third) =
      Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
        thirdWeight third := by
  have denominatorNonzero : 1 - firstWeight ≠ 0 := by
    intro denominatorZero
    apply firstNotOne
    calc
      firstWeight = 1 - (1 - firstWeight) := by ring1
      _ = 1 := by rw [denominatorZero]; ring1
  have denominatorCancel :
      (1 - firstWeight) * (1 - firstWeight)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ denominatorNonzero
  apply Plane.Point.ext
  · unfold Plane.Point.Affine.affineCombination Plane.Point.Affine.affineCombinationThree
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      firstWeight * first.x +
          (1 - firstWeight) *
            (secondWeight * (1 - firstWeight)⁻¹ * second.x +
              thirdWeight * (1 - firstWeight)⁻¹ * third.x) =
        firstWeight * first.x +
          ((1 - firstWeight) * (1 - firstWeight)⁻¹) *
            (secondWeight * second.x + thirdWeight * third.x) := by
              ring1
      _ = firstWeight * first.x + secondWeight * second.x +
          thirdWeight * third.x := by
            rw [denominatorCancel]
            ring1
  · unfold Plane.Point.Affine.affineCombination Plane.Point.Affine.affineCombinationThree
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      firstWeight * first.y +
          (1 - firstWeight) *
            (secondWeight * (1 - firstWeight)⁻¹ * second.y +
              thirdWeight * (1 - firstWeight)⁻¹ * third.y) =
        firstWeight * first.y +
          ((1 - firstWeight) * (1 - firstWeight)⁻¹) *
            (secondWeight * second.y + thirdWeight * third.y) := by
              ring1
      _ = firstWeight * first.y + secondWeight * second.y +
          thirdWeight * third.y := by
            rw [denominatorCancel]
            ring1
/-- Normalizing the remaining two weights by the complement of the first gives weights summing to one.

The original three weights sum to one, and the first weight differs from one. -/
private theorem nestedAffineWeights_sum
    (firstWeight secondWeight thirdWeight : K)
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (firstNotOne : firstWeight ≠ 1) :
    secondWeight / (1 - firstWeight) +
        thirdWeight / (1 - firstWeight) = 1 := by
  have denominatorNonzero : 1 - firstWeight ≠ 0 := by
    intro denominatorZero
    apply firstNotOne
    calc
      firstWeight = 1 - (1 - firstWeight) := by ring1
      _ = 1 := by rw [denominatorZero]; ring1
  have denominatorCancel :
      (1 - firstWeight) * (1 - firstWeight)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ denominatorNonzero
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  have remainingWeights :
      secondWeight + thirdWeight = 1 - firstWeight := by
    calc
      secondWeight + thirdWeight =
          (firstWeight + secondWeight + thirdWeight) - firstWeight := by
            ring1
      _ = 1 - firstWeight := by rw [weightsSum]
  calc
    secondWeight * (1 - firstWeight)⁻¹ +
        thirdWeight * (1 - firstWeight)⁻¹ =
      (secondWeight + thirdWeight) * (1 - firstWeight)⁻¹ := by
        ring1
    _ = (1 - firstWeight) * (1 - firstWeight)⁻¹ := by
      rw [remainingWeights]
    _ = 1 := denominatorCancel
end

/-- Exercise 3.15: all three cyclic nestings of a three-point affine combination have normalized inner weights and
evaluate to the same explicit three-point combination. -/
theorem exercise_3_15
    (firstWeight secondWeight thirdWeight : K)
    (first second third : Point K)
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (firstNotOne : firstWeight ≠ 1)
    (secondNotOne : secondWeight ≠ 1)
    (thirdNotOne : thirdWeight ≠ 1) :
    (secondWeight / (1 - firstWeight) +
        thirdWeight / (1 - firstWeight) = 1) ∧
      (thirdWeight / (1 - secondWeight) +
        firstWeight / (1 - secondWeight) = 1) ∧
      (firstWeight / (1 - thirdWeight) +
        secondWeight / (1 - thirdWeight) = 1) ∧
      Geometry.Plane.Point.Affine.affineCombination firstWeight first (1 - firstWeight)
          (Geometry.Plane.Point.Affine.affineCombination (secondWeight / (1 - firstWeight)) second
            (thirdWeight / (1 - firstWeight)) third) =
        Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
          thirdWeight third ∧
      Geometry.Plane.Point.Affine.affineCombination secondWeight second (1 - secondWeight)
          (Geometry.Plane.Point.Affine.affineCombination (thirdWeight / (1 - secondWeight)) third
            (firstWeight / (1 - secondWeight)) first) =
        Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
          thirdWeight third ∧
      Geometry.Plane.Point.Affine.affineCombination thirdWeight third (1 - thirdWeight)
          (Geometry.Plane.Point.Affine.affineCombination (firstWeight / (1 - thirdWeight)) first
            (secondWeight / (1 - thirdWeight)) second) =
        Plane.Point.Affine.affineCombinationThree firstWeight first secondWeight second
          thirdWeight third := by
  have secondCyclicSum :
      secondWeight + thirdWeight + firstWeight = 1 := by
    calc
      secondWeight + thirdWeight + firstWeight =
          firstWeight + secondWeight + thirdWeight := by ring1
      _ = 1 := weightsSum
  have thirdCyclicSum :
      thirdWeight + firstWeight + secondWeight = 1 := by
    calc
      thirdWeight + firstWeight + secondWeight =
          firstWeight + secondWeight + thirdWeight := by ring1
      _ = 1 := weightsSum
  exact ⟨
    Purelib.Geometry.Plane.Point.Affine.nestedAffineWeights_sum firstWeight secondWeight thirdWeight
      weightsSum firstNotOne,
    Purelib.Geometry.Plane.Point.Affine.nestedAffineWeights_sum secondWeight thirdWeight firstWeight
      secondCyclicSum secondNotOne,
    Purelib.Geometry.Plane.Point.Affine.nestedAffineWeights_sum thirdWeight firstWeight secondWeight
      thirdCyclicSum thirdNotOne,
    Purelib.Geometry.Plane.Point.Affine.nestedAffineCombination_eq_three firstWeight secondWeight thirdWeight
      first second third firstNotOne,
    by
      have cyclic := Purelib.Geometry.Plane.Point.Affine.nestedAffineCombination_eq_three
        secondWeight thirdWeight firstWeight second third first
        secondNotOne
      exact cyclic.trans (by
        apply Plane.Point.ext <;>
          unfold Plane.Point.Affine.affineCombinationThree <;>
          ring1),
    by
      have cyclic := Purelib.Geometry.Plane.Point.Affine.nestedAffineCombination_eq_three
        thirdWeight firstWeight secondWeight third first second
        thirdNotOne
      exact cyclic.trans (by
        apply Plane.Point.ext <;>
          unfold Plane.Point.Affine.affineCombinationThree <;>
          ring1)⟩
end Purelib.Geometry.Plane.Point.Affine

end

end

section
public section

/-!
# Divine Proportions, Theorem 116: the Euler line

The centroid is an explicit finite affine combination.  The key identity is
the source's relation `G = (2/3)C + (1/3)O`, proved first for the already
formalized affine circumcenter and orthocenter weights and then transferred to
the geometric center constructions.  No completed line or infinite locus is
introduced: collinearity is the finite three-point determinant relation.
-/

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- If the combination with weights two thirds and one third fixes its first point, both points agree.

Three is assumed nonzero. -/
theorem points_equal_of_euler_affine_fixed
    (fixed other : Point K) (threeNonzero : (3 : K) ≠ 0)
    (relation :
      Geometry.Plane.Point.Affine.affineCombination ((2 : K) / 3) fixed ((1 : K) / 3) other = fixed) :
    fixed = other := by
  have xRelation := congrArg x relation
  have yRelation := congrArg y relation
  change ((2 : K) / 3) * fixed.x + ((1 : K) / 3) * other.x =
    fixed.x at xRelation
  change ((2 : K) / 3) * fixed.y + ((1 : K) / 3) * other.y =
    fixed.y at yRelation
  have twoCancel : ((2 : K) / 3) * 3 = 2 :=
    Algebra.Field.ExplicitField.div_mul_cancel 2 threeNonzero
  have oneCancel : ((1 : K) / 3) * 3 = 1 :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 threeNonzero
  apply Plane.Point.ext
  · have cleared : 2 * fixed.x + other.x = fixed.x * 3 := by
      calc
        2 * fixed.x + other.x =
            (((2 : K) / 3) * 3) * fixed.x +
              (((1 : K) / 3) * 3) * other.x := by
                rw [twoCancel, oneCancel]
                ring1
        _ = (((2 : K) / 3) * fixed.x +
              ((1 : K) / 3) * other.x) * 3 := by ring1
        _ = fixed.x * 3 := by rw [xRelation]
    calc
      fixed.x = fixed.x * 3 - 2 * fixed.x := by ring1
      _ = other.x := by rw [← cleared]; ring1
  · have cleared : 2 * fixed.y + other.y = fixed.y * 3 := by
      calc
        2 * fixed.y + other.y =
            (((2 : K) / 3) * 3) * fixed.y +
              (((1 : K) / 3) * 3) * other.y := by
                rw [twoCancel, oneCancel]
                ring1
        _ = (((2 : K) / 3) * fixed.y +
              ((1 : K) / 3) * other.y) * 3 := by ring1
        _ = fixed.y * 3 := by rw [yRelation]
    calc
      fixed.y = fixed.y * 3 - 2 * fixed.y := by ring1
      _ = other.y := by rw [← cleared]; ring1

end Purelib.Geometry.Plane.Point.Affine

end

section
public section

/-!
# Divine Proportions, conic axes

An axis is retained as an explicit non-null mirror together with the finite
equation-preservation identity from Exercise 15.8.  The elementary reflection
lemmas below construct the two mirrors used for quadrolas without selecting
any roots or completed geometric object.
-/

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Twice the midpoint's first coordinate is the sum of the endpoint first coordinates when two is nonzero. -/
theorem midpoint_twice_x (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    2 * (Geometry.Plane.Point.Affine.midpoint first second).x = first.x + second.x := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  change 2 * ((first.x + second.x) / 2) = first.x + second.x
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    2 * ((first.x + second.x) * (2 : K)⁻¹) =
        (first.x + second.x) * (2 * (2 : K)⁻¹) := by ring1
    _ = first.x + second.x := by rw [twoCancel]; ring1

/-- Twice the midpoint's second coordinate is the sum of the endpoint second coordinates when two is nonzero. -/
theorem midpoint_twice_y (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    2 * (Geometry.Plane.Point.Affine.midpoint first second).y = first.y + second.y := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  change 2 * ((first.y + second.y) / 2) = first.y + second.y
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    2 * ((first.y + second.y) * (2 : K)⁻¹) =
        (first.y + second.y) * (2 * (2 : K)⁻¹) := by ring1
    _ = first.y + second.y := by rw [twoCancel]; ring1

end Purelib.Geometry.Plane.Point.Affine

end

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Equal midpoints and equal or opposite displacement vectors determine the same unordered endpoint pair.

Two is nonzero, allowing recovery of each endpoint from the sum and difference. -/
theorem endpoint_pairs_of_midpoint_and_difference
    (firstOne firstTwo secondOne secondTwo : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (midpointsEqual : Geometry.Plane.Point.Affine.midpoint firstOne firstTwo = Geometry.Plane.Point.Affine.midpoint
      secondOne secondTwo)
    (differences :
      ((firstTwo.x - firstOne.x = secondTwo.x - secondOne.x ∧
          firstTwo.y - firstOne.y = secondTwo.y - secondOne.y) ∨
        (firstTwo.x - firstOne.x = -(secondTwo.x - secondOne.x) ∧
          firstTwo.y - firstOne.y = -(secondTwo.y - secondOne.y)))) :
    (firstOne = secondOne ∧ firstTwo = secondTwo) ∨
      (firstOne = secondTwo ∧ firstTwo = secondOne) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have sumX : firstOne.x + firstTwo.x = secondOne.x + secondTwo.x := by
    have midpointX := congrArg x midpointsEqual
    have scaled := congrArg (fun value : K => 2 * value) midpointX
    calc
      firstOne.x + firstTwo.x =
          2 * ((firstOne.x + firstTwo.x) / 2) := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        calc
          firstOne.x + firstTwo.x =
              (firstOne.x + firstTwo.x) * (2 * (2 : K)⁻¹) := by
            rw [twoCancel]
            ring1
          _ = 2 * ((firstOne.x + firstTwo.x) * (2 : K)⁻¹) := by ring1
      _ = 2 * ((secondOne.x + secondTwo.x) / 2) := scaled
      _ = secondOne.x + secondTwo.x := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        calc
          2 * ((secondOne.x + secondTwo.x) * (2 : K)⁻¹) =
              (secondOne.x + secondTwo.x) * (2 * (2 : K)⁻¹) := by ring1
          _ = secondOne.x + secondTwo.x := by rw [twoCancel]; ring1
  have sumY : firstOne.y + firstTwo.y = secondOne.y + secondTwo.y := by
    have midpointY := congrArg y midpointsEqual
    have scaled := congrArg (fun value : K => 2 * value) midpointY
    calc
      firstOne.y + firstTwo.y =
          2 * ((firstOne.y + firstTwo.y) / 2) := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        calc
          firstOne.y + firstTwo.y =
              (firstOne.y + firstTwo.y) * (2 * (2 : K)⁻¹) := by
            rw [twoCancel]
            ring1
          _ = 2 * ((firstOne.y + firstTwo.y) * (2 : K)⁻¹) := by ring1
      _ = 2 * ((secondOne.y + secondTwo.y) / 2) := scaled
      _ = secondOne.y + secondTwo.y := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        calc
          2 * ((secondOne.y + secondTwo.y) * (2 : K)⁻¹) =
              (secondOne.y + secondTwo.y) * (2 * (2 : K)⁻¹) := by ring1
          _ = secondOne.y + secondTwo.y := by rw [twoCancel]; ring1
  have orderedCoordinate :
      ∀ (firstLeft firstRight secondLeft secondRight : K),
        firstLeft + firstRight = secondLeft + secondRight →
        firstRight - firstLeft = secondRight - secondLeft →
        firstLeft = secondLeft ∧ firstRight = secondRight := by
    intro firstLeft firstRight secondLeft secondRight sumEqual differenceEqual
    have twiceLeftDifference :
        (2 : K) * (firstLeft - secondLeft) = 0 := by
      calc
        (2 : K) * (firstLeft - secondLeft) =
            (firstLeft + firstRight - (firstRight - firstLeft)) -
              (secondLeft + secondRight - (secondRight - secondLeft)) := by
          ring1
        _ = 0 := by rw [sumEqual, differenceEqual]; ring1
    have leftDifferenceZero :=
      Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceLeftDifference
    have leftEqual : firstLeft = secondLeft := by
      calc
        firstLeft = (firstLeft - secondLeft) + secondLeft := by ring1
        _ = secondLeft := by rw [leftDifferenceZero]; ring1
    have rightEqual : firstRight = secondRight := by
      calc
        firstRight = (firstLeft + firstRight) - firstLeft := by ring1
        _ = (secondLeft + secondRight) - secondLeft := by
          rw [sumEqual, leftEqual]
        _ = secondRight := by ring1
    exact ⟨leftEqual, rightEqual⟩
  rcases differences with ordered | reversed
  · have xCoordinates := orderedCoordinate firstOne.x firstTwo.x
      secondOne.x secondTwo.x sumX ordered.1
    have yCoordinates := orderedCoordinate firstOne.y firstTwo.y
      secondOne.y secondTwo.y sumY ordered.2
    left
    exact ⟨Plane.Point.ext xCoordinates.1 yCoordinates.1,
      Plane.Point.ext xCoordinates.2 yCoordinates.2⟩
  · have reversedX :
        firstTwo.x - firstOne.x = secondOne.x - secondTwo.x := by
      calc
        firstTwo.x - firstOne.x =
            -(secondTwo.x - secondOne.x) := reversed.1
        _ = secondOne.x - secondTwo.x := by ring1
    have reversedY :
        firstTwo.y - firstOne.y = secondOne.y - secondTwo.y := by
      calc
        firstTwo.y - firstOne.y =
            -(secondTwo.y - secondOne.y) := reversed.2
        _ = secondOne.y - secondTwo.y := by ring1
    have xCoordinates := orderedCoordinate firstOne.x firstTwo.x
      secondTwo.x secondOne.x (by rw [sumX]; ring1) reversedX
    have yCoordinates := orderedCoordinate firstOne.y firstTwo.y
      secondTwo.y secondOne.y (by rw [sumY]; ring1) reversedY
    right
    exact ⟨Plane.Point.ext xCoordinates.1 yCoordinates.1,
      Plane.Point.ext xCoordinates.2 yCoordinates.2⟩

end Purelib.Geometry.Plane.Point.Affine

end

section
public section

/-!
# Divine Proportions, Chapter 10: the median triangle

All three midpoint sides are retained as displayed lines.  Their distinctness,
parallelism, and non-nullity are proved explicitly, so the final similarity
statement is a finite triple of spread equalities over any explicit field of
characteristic different from two.
-/

namespace Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Equality of midpoints with a common second endpoint cancels when two is nonzero. This is the finite substitute for
invoking injectivity of an affine homothety. -/
theorem midpoint_cancel_common
    (first second common : Point K) (twoNonzero : (2 : K) ≠ 0)
    (equalMidpoints : Geometry.Plane.Point.Affine.midpoint first common = Geometry.Plane.Point.Affine.midpoint second
      common) :
    first = second := by
  have equalX := congrArg x equalMidpoints
  have equalY := congrArg y equalMidpoints
  change (first.x + common.x) / 2 = (second.x + common.x) / 2 at equalX
  change (first.y + common.y) / 2 = (second.y + common.y) / 2 at equalY
  apply Plane.Point.ext
  · calc
      first.x = ((first.x + common.x) / 2) * 2 - common.x := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
      _ = ((second.x + common.x) / 2) * 2 - common.x := by rw [equalX]
      _ = second.x := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
  · calc
      first.y = ((first.y + common.y) / 2) * 2 - common.y := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
      _ = ((second.y + common.y) / 2) * 2 - common.y := by rw [equalY]
      _ = second.y := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1

/-- Distinct points give distinct midpoints when they share the other endpoint. -/
theorem midpoint_pair_distinct
    (first second common : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Plane.Point.Affine.midpoint first common ≠ Geometry.Plane.Point.Affine.midpoint second common := by
  intro equalMidpoints
  exact distinct
    (Geometry.Plane.Point.Affine.midpoint_cancel_common first second common twoNonzero equalMidpoints)

/-- Exchanging the two endpoints preserves their displayed midpoint. -/
theorem midpoint_symm (first second : Point K) :
    Geometry.Plane.Point.Affine.midpoint first second = Geometry.Plane.Point.Affine.midpoint second first := by
  apply Plane.Point.ext
  · change (first.x + second.x) / 2 = (second.x + first.x) / 2
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  · change (first.y + second.y) / 2 = (second.y + first.y) / 2
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1

/-- The common-first-endpoint form of `midpoint_pair_distinct`. -/
theorem midpoint_pair_distinct_left
    (common first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Plane.Point.Affine.midpoint common first ≠ Geometry.Plane.Point.Affine.midpoint common second := by
  intro equalMidpoints
  apply distinct
  apply Geometry.Plane.Point.Affine.midpoint_cancel_common first second common twoNonzero
  calc
    Geometry.Plane.Point.Affine.midpoint first common = Geometry.Plane.Point.Affine.midpoint common first :=
      Geometry.Plane.Point.Affine.midpoint_symm first common
    _ = Geometry.Plane.Point.Affine.midpoint common second := equalMidpoints
    _ = Geometry.Plane.Point.Affine.midpoint second common := Geometry.Plane.Point.Affine.midpoint_symm common second
end Purelib.Geometry.Plane.Point.Affine

end
