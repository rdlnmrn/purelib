module

import Purelib.Algebra.Field.Midpoint
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
/-!
# Divine Proportions, Exercise 16.6: antipodal quadrance sums

The printed exercise omits a non-null hypothesis.  An executable `F₅`
counterexample below shows that the claim fails on a null circle.  For a
non-null circle, its displayed intersection makes every diameter non-null;
midpoint uniqueness then identifies the two equidistant diameter points as
antipodes, giving an explicit constant quadrance sum.
-/

public section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Curves.Plane.Conic

/-- The polynomial antipodal-sum identity, stated using the two coordinate equations which say that `center` is the
midpoint of `first` and `second`. -/
theorem antipodal_quadrance_sum
    (first second center point : Geometry.Plane.Point K)
    (xSum : first.x + second.x = 2 * center.x)
    (ySum : first.y + second.y = 2 * center.y) :
    Quadrance.quadrance first point + Quadrance.quadrance second point =
      2 * (Quadrance.quadrance first center + Quadrance.quadrance point center) := by
  unfold Quadrance.quadrance
  rw [show second.x = 2 * center.x - first.x by
      calc
        second.x = (first.x + second.x) - first.x := by ring1
        _ = 2 * center.x - first.x := by rw [xSum],
    show second.y = 2 * center.y - first.y by
      calc
        second.y = (first.y + second.y) - first.y := by ring1
        _ = 2 * center.y - first.y := by rw [ySum]]
  ring1

end Purelib.Curves.Plane.Conic

end

end

end

end

section
public section

/-!
# Divine Proportions, §16.2: equal products

The source derives Theorem 106 from subtended spreads and the Spread law.  The
finite algebra underneath that proof is stronger: along any displayed chord,
the product of the two endpoint quadrances is the square of the intersection
point's circle-power.  This form needs no non-null hypotheses or division.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Curves.Plane.Conic

/-- The quadrance from the first endpoint to a Thales point on its line. -/
public theorem quadrance_first_thalesPoint
    (first second : Geometry.Plane.Point K) (scale : K) :
    Quadrance.quadrance first (Affine.thalesPoint scale first second) =
      scale ^ 2 * Quadrance.quadrance first second := by
  unfold Quadrance.quadrance Affine.thalesPoint Affine.affineCombination
  ring1

/-- The quadrance from a Thales point to the second endpoint. -/
public theorem quadrance_thalesPoint_second
    (first second : Geometry.Plane.Point K) (scale : K) :
    Quadrance.quadrance (Affine.thalesPoint scale first second) second =
      (1 - scale) ^ 2 * Quadrance.quadrance first second := by
  unfold Quadrance.quadrance Affine.thalesPoint Affine.affineCombination
  ring1

end Purelib.Curves.Plane.Conic

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

namespace Purelib.Geometry.Plane.Point.Affine.Quadrance

/-- The segment joining two midpoints with a common endpoint has one quarter of the quadrance of the segment joining the
other endpoints. -/
theorem midpoint_segment_quadrance
    (first second common : Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint first common) (Affine.midpoint second common) =
      Quadrance.quadrance first second / 4 := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    Quadrance.quadrance (Affine.midpoint first common) (Affine.midpoint second common) * 4 =
        Quadrance.quadrance first second := by
      unfold Quadrance.quadrance Affine.midpoint
      change
        ((((second.x + common.x) / 2) -
              ((first.x + common.x) / 2)) ^ 2 +
            (((second.y + common.y) / 2) -
              ((first.y + common.y) / 2)) ^ 2) * 4 =
          (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      rw [fourAsProduct]
      calc
        ((((second.x + common.x) * (2 : K)⁻¹) -
                ((first.x + common.x) * (2 : K)⁻¹)) ^ 2 +
              (((second.y + common.y) * (2 : K)⁻¹) -
                ((first.y + common.y) * (2 : K)⁻¹)) ^ 2) * (2 * 2) =
            ((second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2) *
                (2 * (2 : K)⁻¹) ^ 2 := by ring1
        _ = (second.x - first.x) ^ 2 +
            (second.y - first.y) ^ 2 := by rw [twoCancel]; ring1
    _ = (Quadrance.quadrance first second / 4) * 4 :=
      (Algebra.Field.ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- The common-first-endpoint form of `midpoint_segment_quadrance`. -/
theorem midpoint_segment_quadrance_left
    (common first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint common first) (Affine.midpoint common second) =
      Quadrance.quadrance first second / 4 := by
  calc
    Quadrance.quadrance (Affine.midpoint common first) (Affine.midpoint common second) =
        Quadrance.quadrance (Affine.midpoint first common) (Affine.midpoint second common) := by
      rw [Affine.midpoint_symm common first, Affine.midpoint_symm common second]
    _ = Quadrance.quadrance first second / 4 :=
      Geometry.Plane.Point.Affine.Quadrance.midpoint_segment_quadrance first second common twoNonzero

end Purelib.Geometry.Plane.Point.Affine.Quadrance

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

namespace Purelib.Geometry.Plane.Point.Affine.Quadrance

/-- The displayed midpoint has equal quadrance to the two endpoints. -/
theorem midpoint_equal_quadrance
    (first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint first second) first =
      Quadrance.quadrance (Affine.midpoint first second) second := by
  unfold Quadrance.quadrance
  change
    (first.x - (first.x + second.x) / 2) ^ 2 +
        (first.y - (first.y + second.y) / 2) ^ 2 =
      (second.x - (first.x + second.x) / 2) ^ 2 +
        (second.y - (first.y + second.y) / 2) ^ 2
  rw [Purelib.Algebra.Field.Midpoint.left_sub_midpoint_coordinate first.x second.x twoNonzero,
    Purelib.Algebra.Field.Midpoint.left_sub_midpoint_coordinate first.y second.y twoNonzero,
    Purelib.Algebra.Field.Midpoint.right_sub_midpoint_coordinate first.x second.x twoNonzero,
    Purelib.Algebra.Field.Midpoint.right_sub_midpoint_coordinate first.y second.y twoNonzero]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- The midpoint-to-endpoint quadrance is one quarter of the side quadrance. Only characteristic two is excluded. -/
theorem midpoint_quadrance [DecidableEq K]
    (first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint first second) first = Quadrance.quadrance first second / 4 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have scaled : Quadrance.quadrance (Affine.midpoint first second) first * (4 : K) =
      Quadrance.quadrance first second := by
    unfold Quadrance.quadrance
    change
      ((first.x - (first.x + second.x) / 2) ^ 2 +
        (first.y - (first.y + second.y) / 2) ^ 2) * 4 =
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2
    rw [Purelib.Algebra.Field.Midpoint.left_sub_midpoint_coordinate first.x second.x twoNonzero,
      Purelib.Algebra.Field.Midpoint.left_sub_midpoint_coordinate first.y second.y twoNonzero]
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [fourAsProduct]
    calc
      (((first.x - second.x) * (2 : K)⁻¹) ^ 2 +
          ((first.y - second.y) * (2 : K)⁻¹) ^ 2) * (2 * 2) =
        ((first.x - second.x) ^ 2 + (first.y - second.y) ^ 2) *
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [twoInverse]
        ring1
  calc
    Quadrance.quadrance (Affine.midpoint first second) first =
        Quadrance.quadrance (Affine.midpoint first second) first * 4 * (4 : K)⁻¹ := by
      rw [mul_assoc, Algebra.Field.ExplicitField.mul_inv_cancel 4 fourNonzero, mul_one]
    _ = Quadrance.quadrance first second * (4 : K)⁻¹ := by rw [scaled]
    _ = Quadrance.quadrance first second / 4 := by
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv]

/-- The uniqueness clause of Theorem 20: on a non-null side, the midpoint is the only point of the line equidistant from
the endpoints. -/
theorem midpoint_unique_of_equal_quadrance [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (Incidence.lineThrough first second distinct).IsNull)
    (onLine : (Incidence.lineThrough first second distinct).Contains point)
    (equalQuadrances : Quadrance.quadrance point first = Quadrance.quadrance point second) :
    point = Affine.midpoint first second := by
  have sideQuadranceNonzero : Quadrance.quadrance first second ≠ 0 := by
    intro sideQuadranceZero
    exact sideNonNull
      ((Quadrance.null_line_iff_quadrance_zero first second distinct).2 sideQuadranceZero)
  rcases Affine.affineWeights_exist first second point distinct onLine with
    ⟨leftWeight, rightWeight, weights, combination⟩
  have leftFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weights]
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  have fromFirst : Quadrance.quadrance point first =
      rightWeight ^ 2 * Quadrance.quadrance first second := by
    rw [← combination]
    rw [leftFormula]
    unfold Quadrance.quadrance Affine.affineCombination
    ring1
  have fromSecond : Quadrance.quadrance point second =
      leftWeight ^ 2 * Quadrance.quadrance first second := by
    rw [← combination]
    rw [rightFormula]
    unfold Quadrance.quadrance Affine.affineCombination
    ring1
  have differenceTimesSide :
      (rightWeight ^ 2 - leftWeight ^ 2) * Quadrance.quadrance first second = 0 := by
    calc
      (rightWeight ^ 2 - leftWeight ^ 2) * Quadrance.quadrance first second =
          rightWeight ^ 2 * Quadrance.quadrance first second -
            leftWeight ^ 2 * Quadrance.quadrance first second := by ring1
      _ = Quadrance.quadrance point first - Quadrance.quadrance point second := by
        rw [fromFirst, fromSecond]
      _ = 0 := by rw [equalQuadrances]; ring1
  have squareDifferenceZero : rightWeight ^ 2 - leftWeight ^ 2 = 0 :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {left right : K} (rightNonzero : right ≠
      0) (productZero : left * right = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right (K := K)
      (left := left) (right := right) rightNonzero productZero : left = 0)) sideQuadranceNonzero differenceTimesSide
  have weightsReversed : rightWeight + leftWeight = 1 := by
    calc
      rightWeight + leftWeight = leftWeight + rightWeight := by ring1
      _ = 1 := weights
  have weightDifferenceZero : rightWeight - leftWeight = 0 := by
    have productZero :
        (rightWeight - leftWeight) * (rightWeight + leftWeight) = 0 := by
      calc
        (rightWeight - leftWeight) * (rightWeight + leftWeight) =
            rightWeight ^ 2 - leftWeight ^ 2 := by ring1
        _ = 0 := squareDifferenceZero
    rw [weightsReversed, mul_one] at productZero
    exact productZero
  have weightsEqual : rightWeight = leftWeight := by
    calc
      rightWeight = (rightWeight - leftWeight) + leftWeight := by ring1
      _ = leftWeight := by rw [weightDifferenceZero]; ring1
  have twiceLeft : (2 : K) * leftWeight = 1 := by
    calc
      (2 : K) * leftWeight = leftWeight + rightWeight := by
        rw [weightsEqual]
        ring1
      _ = 1 := weights
  have leftTimesTwo : leftWeight * (2 : K) = 1 := by
    calc
      leftWeight * (2 : K) = (2 : K) * leftWeight := by ring1
      _ = 1 := twiceLeft
  have halfTimesTwo : ((1 : K) / 2) * 2 = 1 :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 twoNonzero
  have leftIsHalf : leftWeight = (1 : K) / 2 := by
    have differenceTimesTwo : (leftWeight - (1 : K) / 2) * 2 = 0 := by
      calc
        (leftWeight - (1 : K) / 2) * 2 =
            leftWeight * 2 - ((1 : K) / 2) * 2 := by ring1
        _ = 0 := by rw [leftTimesTwo, halfTimesTwo]; ring1
    have differenceZero :=
      (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {left right : K} (rightNonzero : right ≠
        0) (productZero : left * right = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_right (K :=
        K) (left := left) (right := right) rightNonzero productZero : left = 0)) twoNonzero differenceTimesTwo
    calc
      leftWeight = (leftWeight - (1 : K) / 2) + (1 : K) / 2 := by ring1
      _ = (1 : K) / 2 := by rw [differenceZero]; ring1
  rw [← combination, weightsEqual, leftIsHalf]
  apply Plane.Point.ext <;>
    simp only [Affine.affineCombination, Affine.midpoint,
      Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- Theorem 20 (Midpoint), collecting existence, metric value, and uniqueness in one finite statement. -/
theorem midpoint_theorem [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    (Incidence.lineThrough first second distinct).Contains (Affine.midpoint first second) ∧
      Quadrance.quadrance (Affine.midpoint first second) first =
        Quadrance.quadrance (Affine.midpoint first second) second ∧
      Quadrance.quadrance (Affine.midpoint first second) first = Quadrance.quadrance first second / 4 ∧
      ∀ point : Point K,
        (Incidence.lineThrough first second distinct).Contains point →
        Quadrance.quadrance point first = Quadrance.quadrance point second →
        point = Affine.midpoint first second := by
  exact ⟨Affine.midpoint_on_line first second distinct twoNonzero,
    Geometry.Plane.Point.Affine.Quadrance.midpoint_equal_quadrance first second twoNonzero,
    Geometry.Plane.Point.Affine.Quadrance.midpoint_quadrance first second twoNonzero,
    fun point onLine equalQuadrances =>
      Geometry.Plane.Point.Affine.Quadrance.midpoint_unique_of_equal_quadrance first second point distinct
        twoNonzero sideNonNull onLine equalQuadrances⟩

end Purelib.Geometry.Plane.Point.Affine.Quadrance

end

end

end

section
public section

/-!
# Divine Proportions, Chapter 5 triangle exercises

The centroid calculation is reduced to two finite affine-scaling identities.
All divisions retain explicit characteristic-two and characteristic-three
certificates.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Point.Affine.Quadrance

/-- For weights summing to one, the quadrance from the first endpoint to the combination is the squared second weight
times the endpoint quadrance. -/
public theorem quadrance_affineCombination_left
    (left right : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    Quadrance.quadrance left
        (Affine.affineCombination leftWeight left rightWeight right) =
      rightWeight ^ 2 * Quadrance.quadrance left right := by
  have leftWeightFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weightsSum]
  rw [leftWeightFormula]
  unfold Quadrance.quadrance Affine.affineCombination
  ring1

/-- For weights summing to one, the quadrance from the combination to the second endpoint is the squared first weight
times the endpoint quadrance. -/
public theorem quadrance_affineCombination_right
    (left right : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    Quadrance.quadrance
        (Affine.affineCombination leftWeight left rightWeight right) right =
      leftWeight ^ 2 * Quadrance.quadrance left right := by
  have rightWeightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weightsSum]
  rw [rightWeightFormula]
  unfold Quadrance.quadrance Affine.affineCombination
  ring1

end Purelib.Geometry.Plane.Point.Affine.Quadrance

end

end

end

end
