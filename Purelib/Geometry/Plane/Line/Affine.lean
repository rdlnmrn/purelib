module
import Purelib.Algebra.Group.Basic
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

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

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Affine

/-- Any two displayed points and an affine combination with weights summing to one are collinear, including the case
where the first two points coincide. -/
theorem collinear_affineCombination
    [Nontrivial K] [DecidableEq K]
    (first second : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    Incidence.Collinear first second
      (Affine.affineCombination leftWeight first rightWeight second) := by
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second
    (Affine.affineCombination leftWeight first rightWeight second)).2
  unfold Incidence.pointDeterminant
  change
    first.x * second.y -
          first.x * (leftWeight * first.y + rightWeight * second.y) +
        second.x * (leftWeight * first.y + rightWeight * second.y) -
          (leftWeight * first.x + rightWeight * second.x) * second.y +
        (leftWeight * first.x + rightWeight * second.x) * first.y -
      second.x * first.y = 0
  calc
    first.x * second.y -
          first.x * (leftWeight * first.y + rightWeight * second.y) +
        second.x * (leftWeight * first.y + rightWeight * second.y) -
          (leftWeight * first.x + rightWeight * second.x) * second.y +
        (leftWeight * first.x + rightWeight * second.x) * first.y -
          second.x * first.y =
      (leftWeight + rightWeight - 1) *
        (second.x * first.y - first.x * second.y) := by ring1
    _ = 0 := by rw [weightsSum]; ring1

end Purelib.Geometry.Plane.Line.Affine

end

end

section
public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Affine

/-- Any displayed line containing two points also contains their midpoint. -/
theorem line_contains_midpoint
    (line : Line K) (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    line.Contains (Affine.midpoint first second) := by
  unfold Contains at containsFirst containsSecond ⊢
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right twoNonzero
  calc
    (line.a * (Affine.midpoint first second).x +
          line.b * (Affine.midpoint first second).y + line.c) * 2 =
      (line.a * first.x + line.b * first.y + line.c) +
        (line.a * second.x + line.b * second.y + line.c) := by
          change (line.a * ((first.x + second.x) / 2) +
            line.b * ((first.y + second.y) / 2) + line.c) * 2 = _
          calc
            (line.a * ((first.x + second.x) / 2) +
                line.b * ((first.y + second.y) / 2) + line.c) * 2 =
              line.a * (((first.x + second.x) / 2) * 2) +
                line.b * (((first.y + second.y) / 2) * 2) +
                line.c * 2 := by ring1
            _ = _ := by
              rw [Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero,
                Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero]
              ring1
    _ = 0 := by rw [containsFirst, containsSecond]; ring1
    _ = 0 * 2 := by ring1

end Purelib.Geometry.Plane.Line.Affine

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

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Affine

/-- Barycentric weights relative to three non-collinear points are unique. This is the finite coordinate fact needed to
read geometric triangle membership back into the displayed affine weights. -/
theorem affineCombinationThree_weights_unique [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    {firstWeight secondWeight thirdWeight : K}
    {otherFirstWeight otherSecondWeight otherThirdWeight : K}
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (otherWeightsSum :
      otherFirstWeight + otherSecondWeight + otherThirdWeight = 1)
    (pointsEqual :
      Affine.affineCombinationThree firstWeight first secondWeight second
          thirdWeight third =
        Affine.affineCombinationThree otherFirstWeight first otherSecondWeight second
          otherThirdWeight third) :
    firstWeight = otherFirstWeight ∧
      secondWeight = otherSecondWeight ∧
      thirdWeight = otherThirdWeight := by
  let firstDifference := firstWeight - otherFirstWeight
  let secondDifference := secondWeight - otherSecondWeight
  let thirdDifference := thirdWeight - otherThirdWeight
  have differenceSum :
      firstDifference + secondDifference + thirdDifference = 0 := by
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) +
            (secondWeight - otherSecondWeight) +
            (thirdWeight - otherThirdWeight) =
          (firstWeight + secondWeight + thirdWeight) -
            (otherFirstWeight + otherSecondWeight + otherThirdWeight) := by
              ring1
      _ = 0 := by rw [weightsSum, otherWeightsSum]; ring1
  have xDifference :
      firstDifference * first.x + secondDifference * second.x +
          thirdDifference * third.x = 0 := by
    have coordinateEquality := congrArg Point.x pointsEqual
    simp only [Affine.affineCombinationThree_x] at coordinateEquality
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) * first.x +
            (secondWeight - otherSecondWeight) * second.x +
            (thirdWeight - otherThirdWeight) * third.x =
          (firstWeight * first.x + secondWeight * second.x +
              thirdWeight * third.x) -
            (otherFirstWeight * first.x + otherSecondWeight * second.x +
              otherThirdWeight * third.x) := by ring1
      _ = 0 := by rw [coordinateEquality]; ring1
  have yDifference :
      firstDifference * first.y + secondDifference * second.y +
          thirdDifference * third.y = 0 := by
    have coordinateEquality := congrArg Point.y pointsEqual
    simp only [Affine.affineCombinationThree_y] at coordinateEquality
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) * first.y +
            (secondWeight - otherSecondWeight) * second.y +
            (thirdWeight - otherThirdWeight) * third.y =
          (firstWeight * first.y + secondWeight * second.y +
              thirdWeight * third.y) -
            (otherFirstWeight * first.y + otherSecondWeight * second.y +
              otherThirdWeight * third.y) := by ring1
      _ = 0 := by rw [coordinateEquality]; ring1
  have xReduced :
      firstDifference * (first.x - third.x) +
          secondDifference * (second.x - third.x) = 0 := by
    calc
      firstDifference * (first.x - third.x) +
            secondDifference * (second.x - third.x) =
          (firstDifference * first.x + secondDifference * second.x +
              thirdDifference * third.x) -
            (firstDifference + secondDifference + thirdDifference) *
              third.x := by ring1
      _ = 0 := by rw [xDifference, differenceSum]; ring1
  have yReduced :
      firstDifference * (first.y - third.y) +
          secondDifference * (second.y - third.y) = 0 := by
    calc
      firstDifference * (first.y - third.y) +
            secondDifference * (second.y - third.y) =
          (firstDifference * first.y + secondDifference * second.y +
              thirdDifference * third.y) -
            (firstDifference + secondDifference + thirdDifference) *
              third.y := by ring1
      _ = 0 := by rw [yDifference, differenceSum]; ring1
  have determinantNonzero : Incidence.pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
        determinantZero)
  have firstProduct :
      firstDifference * Incidence.pointDeterminant first second third = 0 := by
    calc
      firstDifference * Incidence.pointDeterminant first second third =
          (firstDifference * (first.x - third.x) +
              secondDifference * (second.x - third.x)) *
              (second.y - third.y) -
            (firstDifference * (first.y - third.y) +
              secondDifference * (second.y - third.y)) *
              (second.x - third.x) := by
                unfold Incidence.pointDeterminant
                ring1
      _ = 0 := by rw [xReduced, yReduced]; ring1
  have secondProduct :
      secondDifference * Incidence.pointDeterminant first second third = 0 := by
    calc
      secondDifference * Incidence.pointDeterminant first second third =
          (firstDifference * (first.y - third.y) +
              secondDifference * (second.y - third.y)) *
              (first.x - third.x) -
            (firstDifference * (first.x - third.x) +
              secondDifference * (second.x - third.x)) *
              (first.y - third.y) := by
                unfold Incidence.pointDeterminant
                ring1
      _ = 0 := by rw [xReduced, yReduced]; ring1
  have firstDifferenceZero : firstDifference = 0 :=
    Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right determinantNonzero firstProduct
  have secondDifferenceZero : secondDifference = 0 :=
    Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right determinantNonzero
      secondProduct
  have thirdDifferenceZero : thirdDifference = 0 := by
    calc
      thirdDifference =
          firstDifference + secondDifference + thirdDifference := by
            rw [firstDifferenceZero, secondDifferenceZero]
            ring1
      _ = 0 := differenceSum
  exact ⟨Purelib.Algebra.Group.eq_of_sub_eq_zero firstDifferenceZero,
    Purelib.Algebra.Group.eq_of_sub_eq_zero secondDifferenceZero,
    Purelib.Algebra.Group.eq_of_sub_eq_zero thirdDifferenceZero⟩

/-- The easy direction of Theorem 9: weights summing to one produce a point on the line through the two source points.
-/
theorem affineCombination_on_line [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (leftWeight rightWeight : K) (weights : leftWeight + rightWeight = 1) :
    (Incidence.lineThrough first second distinct).Contains
      (Affine.affineCombination leftWeight first rightWeight second) := by
  unfold Contains Incidence.lineThrough Affine.affineCombination
  calc
    (first.y - second.y) *
          (leftWeight * first.x + rightWeight * second.x) +
        (second.x - first.x) *
          (leftWeight * first.y + rightWeight * second.y) +
        (first.x * second.y - second.x * first.y) =
      (leftWeight + rightWeight - 1) *
        (second.x * first.y - first.x * second.y) := by ring1
    _ = 0 := by rw [weights]; ring1

/-- Construct the affine weights of an arbitrary point on a line. -/
theorem affineWeights_exist [DecidableEq K]
    (first second point : Plane.Point K) (distinct : first ≠ second)
    (onLine : (Incidence.lineThrough first second distinct).Contains point) :
    ∃ leftWeight rightWeight : K,
      leftWeight + rightWeight = 1 ∧
      Affine.affineCombination leftWeight first rightWeight second = point := by
  unfold Contains Incidence.lineThrough at onLine
  change (first.y - second.y) * point.x +
      (second.x - first.x) * point.y +
      (first.x * second.y - second.x * first.y) = 0 at onLine
  have onLineExpanded :
      (first.y - second.y) * point.x +
        (second.x - first.x) * point.y +
        first.x * second.y - second.x * first.y = 0 := by
    calc
      (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          first.x * second.y - second.x * first.y =
        (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y) := by ring1
      _ = 0 := onLine
  by_cases sameX : first.x = second.x
  · have differentY : first.y ≠ second.y := by
      intro sameY
      apply distinct
      exact Plane.Point.ext sameX sameY
    let denominator := first.y - second.y
    have denominatorNonzero : denominator ≠ 0 := sub_ne_zero_of_ne differentY
    have inverseCancel : denominator⁻¹ * denominator = (1 : K) := by
      calc
        denominator⁻¹ * denominator = denominator * denominator⁻¹ := by ring1
        _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel denominator denominatorNonzero
    let leftWeight := (point.y - second.y) / denominator
    let rightWeight := 1 - leftWeight
    refine ⟨leftWeight, rightWeight, by unfold rightWeight; ring1, ?_⟩
    apply Plane.Point.ext
    · have clearedX :
          denominator * (point.x - second.x) =
            (first.x - second.x) * (point.y - second.y) := by
        unfold denominator
        calc
          (first.y - second.y) * (point.x - second.x) =
              (first.x - second.x) * (point.y - second.y) +
                ((first.y - second.y) * point.x +
                  (second.x - first.x) * point.y +
                  first.x * second.y - second.x * first.y) := by ring1
          _ = (first.x - second.x) * (point.y - second.y) := by
            rw [onLineExpanded]
            ring1
      dsimp only [Affine.affineCombination, leftWeight, rightWeight]
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        (point.y - second.y) * denominator⁻¹ * first.x +
            (1 - (point.y - second.y) * denominator⁻¹) * second.x =
          second.x + denominator⁻¹ *
            ((first.x - second.x) * (point.y - second.y)) := by ring1
        _ = second.x + denominator⁻¹ *
            (denominator * (point.x - second.x)) := by rw [clearedX]
        _ = point.x := by
          rw [← mul_assoc, inverseCancel]
          ring1
    · dsimp only [Affine.affineCombination, leftWeight, rightWeight]
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        (point.y - second.y) * denominator⁻¹ * first.y +
            (1 - (point.y - second.y) * denominator⁻¹) * second.y =
          second.y + denominator⁻¹ *
            (denominator * (point.y - second.y)) := by
          unfold denominator
          ring1
        _ = point.y := by
          rw [← mul_assoc, inverseCancel]
          ring1
  · let denominator := first.x - second.x
    have denominatorNonzero : denominator ≠ 0 := sub_ne_zero_of_ne sameX
    have inverseCancel : denominator⁻¹ * denominator = (1 : K) := by
      calc
        denominator⁻¹ * denominator = denominator * denominator⁻¹ := by ring1
        _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel denominator denominatorNonzero
    let leftWeight := (point.x - second.x) / denominator
    let rightWeight := 1 - leftWeight
    refine ⟨leftWeight, rightWeight, by unfold rightWeight; ring1, ?_⟩
    apply Plane.Point.ext
    · dsimp only [Affine.affineCombination, leftWeight, rightWeight]
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        (point.x - second.x) * denominator⁻¹ * first.x +
            (1 - (point.x - second.x) * denominator⁻¹) * second.x =
          second.x + denominator⁻¹ *
            (denominator * (point.x - second.x)) := by
          unfold denominator
          ring1
        _ = point.x := by
          rw [← mul_assoc, inverseCancel]
          ring1
    · have clearedY :
          denominator * (point.y - second.y) =
            (first.y - second.y) * (point.x - second.x) := by
        unfold denominator
        calc
          (first.x - second.x) * (point.y - second.y) =
              (first.y - second.y) * (point.x - second.x) -
                ((first.y - second.y) * point.x +
                  (second.x - first.x) * point.y +
                  first.x * second.y - second.x * first.y) := by ring1
          _ = (first.y - second.y) * (point.x - second.x) := by
            rw [onLineExpanded]
            ring1
      dsimp only [Affine.affineCombination, leftWeight, rightWeight]
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        (point.x - second.x) * denominator⁻¹ * first.y +
            (1 - (point.x - second.x) * denominator⁻¹) * second.y =
          second.y + denominator⁻¹ *
            ((first.y - second.y) * (point.x - second.x)) := by ring1
        _ = second.y + denominator⁻¹ *
            (denominator * (point.y - second.y)) := by rw [clearedY]
        _ = point.y := by
          rw [← mul_assoc, inverseCancel]
          ring1

/-- The weights in Theorem 9 are unique. -/
theorem affineWeights_unique [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    {leftWeight rightWeight otherLeftWeight otherRightWeight : K}
    (weights : leftWeight + rightWeight = 1)
    (otherWeights : otherLeftWeight + otherRightWeight = 1)
    (samePoint :
      Affine.affineCombination leftWeight first rightWeight second =
        Affine.affineCombination otherLeftWeight first otherRightWeight second) :
    leftWeight = otherLeftWeight ∧ rightWeight = otherRightWeight := by
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  have otherRightFormula : otherRightWeight = 1 - otherLeftWeight := by
    calc
      otherRightWeight =
          (otherLeftWeight + otherRightWeight) - otherLeftWeight := by ring1
      _ = 1 - otherLeftWeight := by rw [otherWeights]
  have sameX := congrArg Point.x samePoint
  have sameY := congrArg Point.y samePoint
  simp only [Affine.affineCombination_x, rightFormula, otherRightFormula] at sameX
  simp only [Affine.affineCombination_y, rightFormula, otherRightFormula] at sameY
  have xProductZero :
      (leftWeight - otherLeftWeight) * (first.x - second.x) = 0 := by
    calc
      (leftWeight - otherLeftWeight) * (first.x - second.x) =
          (leftWeight * first.x + (1 - leftWeight) * second.x) -
            (otherLeftWeight * first.x +
              (1 - otherLeftWeight) * second.x) := by ring1
      _ = 0 := by rw [sameX]; ring1
  have yProductZero :
      (leftWeight - otherLeftWeight) * (first.y - second.y) = 0 := by
    calc
      (leftWeight - otherLeftWeight) * (first.y - second.y) =
          (leftWeight * first.y + (1 - leftWeight) * second.y) -
            (otherLeftWeight * first.y +
              (1 - otherLeftWeight) * second.y) := by ring1
      _ = 0 := by rw [sameY]; ring1
  have leftEqual : leftWeight = otherLeftWeight := by
    by_cases sameXCoordinate : first.x = second.x
    · have differentY : first.y ≠ second.y := by
        intro sameYCoordinate
        exact distinct (Point.ext sameXCoordinate sameYCoordinate)
      have differenceZero := Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right
        (sub_ne_zero_of_ne differentY) yProductZero
      calc
        leftWeight = (leftWeight - otherLeftWeight) + otherLeftWeight := by ring1
        _ = otherLeftWeight := by rw [differenceZero]; ring1
    · have differenceZero := Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right
        (sub_ne_zero_of_ne sameXCoordinate) xProductZero
      calc
        leftWeight = (leftWeight - otherLeftWeight) + otherLeftWeight := by ring1
        _ = otherLeftWeight := by rw [differenceZero]; ring1
  exact ⟨leftEqual, by rw [rightFormula, otherRightFormula, leftEqual]⟩

/-- A point lies on the line through two distinct endpoints exactly when it is their affine combination.

The two scalar weights are explicit witnesses whose sum is one. -/
theorem affineCombination_iff_on_line [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second) :
    (Incidence.lineThrough first second distinct).Contains point ↔
      ∃ leftWeight rightWeight : K,
        leftWeight + rightWeight = 1 ∧
        Affine.affineCombination leftWeight first rightWeight second = point := by
  constructor
  · exact Geometry.Plane.Line.Affine.affineWeights_exist first second point distinct
  · rintro ⟨leftWeight, rightWeight, weights, rfl⟩
    exact Geometry.Plane.Line.Affine.affineCombination_on_line first second distinct leftWeight rightWeight weights

/-- The point a fraction `scale` of the way from `origin` to `target`. -/
@[expose] def thalesPoint (scale : K) (origin target : Point K) : Point K :=
  Affine.affineCombination (1 - scale) origin scale target

end Purelib.Geometry.Plane.Line.Affine

section

namespace Purelib.Geometry.Plane.Line.Affine
/-- A nonzero affine scaling about a common origin preserves distinct endpoints. -/
private theorem thales_points_distinct [DecidableEq K]
    (scale : K) (origin second third : Point K)
    (scaleNonzero : scale ≠ 0) (secondThirdDistinct : second ≠ third) :
    Geometry.Plane.Line.Affine.thalesPoint scale origin second ≠ Geometry.Plane.Line.Affine.thalesPoint scale origin
      third := by
  intro equalPoints
  have equalX := congrArg Point.x equalPoints
  have equalY := congrArg Point.y equalPoints
  change (1 - scale) * origin.x + scale * second.x =
    (1 - scale) * origin.x + scale * third.x at equalX
  change (1 - scale) * origin.y + scale * second.y =
    (1 - scale) * origin.y + scale * third.y at equalY
  have xProductZero : scale * (second.x - third.x) = 0 := by
    calc
      scale * (second.x - third.x) =
          ((1 - scale) * origin.x + scale * second.x) -
            ((1 - scale) * origin.x + scale * third.x) := by ring1
      _ = 0 := by rw [equalX]; ring1
  have yProductZero : scale * (second.y - third.y) = 0 := by
    calc
      scale * (second.y - third.y) =
          ((1 - scale) * origin.y + scale * second.y) -
            ((1 - scale) * origin.y + scale * third.y) := by ring1
      _ = 0 := by rw [equalY]; ring1
  by_cases sameX : second.x = third.x
  · have differentY : second.y ≠ third.y := by
      intro sameY
      exact secondThirdDistinct (Point.ext sameX sameY)
    exact (Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero
      (sub_ne_zero_of_ne differentY)) yProductZero
  · exact (Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero
      (sub_ne_zero_of_ne sameX)) xProductZero
end Purelib.Geometry.Plane.Line.Affine

end

namespace Purelib.Geometry.Plane.Line.Affine

/-- Theorem 10 (Thales): corresponding affine points determine a line parallel to the line through the two targets. -/
theorem thales_parallel [DecidableEq K]
    (scale : K) (origin second third : Point K)
    (scaleNonzero : scale ≠ 0) (secondThirdDistinct : second ≠ third) :
    (Incidence.lineThrough (Affine.thalesPoint scale origin second)
        (Affine.thalesPoint scale origin third)
        (by
          exact Purelib.Geometry.Plane.Line.Affine.thales_points_distinct scale origin second third scaleNonzero
            secondThirdDistinct)).Parallel
      (Incidence.lineThrough second third secondThirdDistinct) := by
  unfold Parallel Incidence.lineThrough Affine.thalesPoint Affine.affineCombination
  ring1

end Purelib.Geometry.Plane.Line.Affine

end

end

end

section
section
public section

/-!
# Divine Proportions, §15.6: intersections with lines

The restriction of a conic to a displayed line parameter is handled by one
finite interpolation identity.  Thus Theorem 102 needs no completed polynomial
object and no general theorem about a globally collected root set.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Geometry.Plane.Line.Affine.Conic

/-- Every point on a displayed line through two distinct points has one finite Thales parameter. -/
theorem thalesPoint_exists_of_on_line [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (onLine : (Incidence.lineThrough first second distinct).Contains point) :
    ∃ scale : K, Affine.thalesPoint scale first second = point := by
  rcases (Geometry.Plane.Line.Affine.affineCombination_iff_on_line first second point distinct).1 onLine with
    ⟨leftWeight, rightWeight, weights, combination⟩
  have leftFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weights]
  refine ⟨rightWeight, ?_⟩
  unfold Affine.thalesPoint
  rw [← leftFormula]
  exact combination

/-- The affine line parameter at zero is its first endpoint. -/
@[simp] theorem thalesPoint_zero (first second : Point K) :
    Affine.thalesPoint 0 first second = first := by
  apply Point.ext <;> unfold Affine.thalesPoint Affine.affineCombination <;> ring1

/-- The affine line parameter at one is its second endpoint. -/
@[simp] theorem thalesPoint_one (first second : Point K) :
    Affine.thalesPoint 1 first second = second := by
  apply Point.ext <;> unfold Affine.thalesPoint Affine.affineCombination <;> ring1

end Purelib.Geometry.Plane.Line.Affine.Conic

end

end

end

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

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Affine

/-- The midpoint segment is parallel to the segment between the other two endpoints. This is the half-way instance of
Thales' theorem. -/
theorem midpoint_segment_parallel [DecidableEq K]
    (first second common : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (Incidence.lineThrough (Affine.midpoint first common) (Affine.midpoint second common)
        (Affine.midpoint_pair_distinct first second common distinct twoNonzero)).Parallel
      (Incidence.lineThrough first second distinct) := by
  unfold Parallel Incidence.lineThrough Affine.midpoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- The common-first-endpoint form of `midpoint_segment_parallel`. -/
theorem midpoint_segment_parallel_left [DecidableEq K]
    (common first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (Incidence.lineThrough (Affine.midpoint common first) (Affine.midpoint common second)
        (Affine.midpoint_pair_distinct_left common first second distinct
          twoNonzero)).Parallel
      (Incidence.lineThrough first second distinct) := by
  unfold Parallel Incidence.lineThrough Affine.midpoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

end Purelib.Geometry.Plane.Line.Affine

end

end

section
public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Affine

/-- The displayed midpoint lies on its side line. -/
theorem midpoint_on_line [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (Incidence.lineThrough first second distinct).Contains (Affine.midpoint first second) := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold Contains Incidence.lineThrough Affine.midpoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (first.y - second.y) * ((first.x + second.x) * (2 : K)⁻¹) +
        (second.x - first.x) * ((first.y + second.y) * (2 : K)⁻¹) +
        (first.x * second.y - second.x * first.y) =
      (1 - 2 * (2 : K)⁻¹) *
        (first.x * second.y - second.x * first.y) := by ring1
    _ = 0 := by rw [twoInverse]; ring1

end Purelib.Geometry.Plane.Line.Affine

end

end

end

end
