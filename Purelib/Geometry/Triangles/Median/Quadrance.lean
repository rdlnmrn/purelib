module

import Purelib.Algebra.Field.Midpoint
public import Purelib.Geometry.Plane.Medians
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: right triangles

The midpoint characterization is proved after clearing the finite factor
four.  The intermediate median-quadrance identity is useful again for the
later Median quadrance theorem.
-/

namespace Purelib.Geometry.Triangles.Median.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Denominator-cleared median quadrance identity. -/
theorem median_quadrance_cleared
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint first second) third * 4 =
      2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
        Quadrance.quadrance first second := by
  rw [show (4 : K) = 2 * 2 by ring1]
  unfold Quadrance.quadrance Affine.midpoint
  change
    ((third.x - (first.x + second.x) / 2) ^ 2 +
        (third.y - (first.y + second.y) / 2) ^ 2) * (2 * 2) =
      2 * ((third.x - first.x) ^ 2 + (third.y - first.y) ^ 2) +
        2 * ((third.x - second.x) ^ 2 + (third.y - second.y) ^ 2) -
        ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2)
  calc
    ((third.x - (first.x + second.x) / 2) ^ 2 +
          (third.y - (first.y + second.y) / 2) ^ 2) * (2 * 2) =
      ((third.x - (first.x + second.x) / 2) * 2) ^ 2 +
        ((third.y - (first.y + second.y) / 2) * 2) ^ 2 := by ring1
    _ = (2 * third.x - first.x - second.x) ^ 2 +
        (2 * third.y - first.y - second.y) ^ 2 := by
      rw [(fun {K : Type _} [ExplicitField K] (first second target : K) (twoNonzero : (2 : K) ≠ 0)
        => (Purelib.Algebra.Field.Midpoint.target_sub_half_sum_mul_two (K := K) first second target twoNonzero : (target
        - (first + second) / 2) * 2 = 2 * target - first - second)) first.x second.x third.x
        twoNonzero,
        (fun {K : Type _} [ExplicitField K] (first second target : K) (twoNonzero : (2 : K) ≠ 0)
          => (Purelib.Algebra.Field.Midpoint.target_sub_half_sum_mul_two (K := K) first second target twoNonzero :
          (target - (first + second) / 2) * 2 = 2 * target - first - second)) first.y second.y third.y
          twoNonzero]
    _ = 2 * ((third.x - first.x) ^ 2 + (third.y - first.y) ^ 2) +
        2 * ((third.x - second.x) ^ 2 + (third.y - second.y) ^ 2) -
        ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by ring1
end Purelib.Geometry.Triangles.Median.Quadrance

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: median quadrance

The denominator-cleared identity already proved for right midpoints gives the
median formula directly.  The source's extra `Q₁ ≠ 0` hypothesis is not needed;
only characteristic two is excluded so that the displayed midpoint and `/4`
normalization have their intended meaning.
-/

namespace Purelib.Geometry.Triangles.Median.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Theorem 76 (Median quadrance), with `A₁` as the vertex and `M₁` the midpoint of `A₂A₃`. -/
theorem median_quadrance
    (first second third : Geometry.Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance first (Affine.midpoint second third) =
      (2 * (Quadrance.quadrance first third + Quadrance.quadrance first second) -
        Quadrance.quadrance second third) / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    Quadrance.quadrance first (Affine.midpoint second third) * 4 =
        Quadrance.quadrance (Affine.midpoint second third) first * 4 := by
      rw [Quadrance.quadrance_symm first (Affine.midpoint second third)]
    _ = 2 * Quadrance.quadrance second first + 2 * Quadrance.quadrance third first -
        Quadrance.quadrance second third :=
      median_quadrance_cleared second third first twoNonzero
    _ = 2 * (Quadrance.quadrance first third + Quadrance.quadrance first second) -
        Quadrance.quadrance second third := by
      rw [Quadrance.quadrance_symm second first, Quadrance.quadrance_symm third first]
      ring1
    _ = ((2 * (Quadrance.quadrance first third + Quadrance.quadrance first second) -
        Quadrance.quadrance second third) / 4) * 4 :=
      (ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- Denominator-free form of Exercise 11.7: the sum of the three median quadrances is three quarters of the sum of the
side quadrances. -/
theorem exercise_11_7_cleared
    (first second third : Geometry.Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    (Quadrance.quadrance first (Affine.midpoint second third) +
        Quadrance.quadrance second (Affine.midpoint first third) +
        Quadrance.quadrance third (Affine.midpoint first second)) * 4 =
      3 * (Quadrance.quadrance second third + Quadrance.quadrance first third +
        Quadrance.quadrance first second) := by
  rw [Quadrance.quadrance_symm first (Affine.midpoint second third),
    Quadrance.quadrance_symm second (Affine.midpoint first third),
    Quadrance.quadrance_symm third (Affine.midpoint first second)]
  calc
    (Quadrance.quadrance (Affine.midpoint second third) first +
          Quadrance.quadrance (Affine.midpoint first third) second +
          Quadrance.quadrance (Affine.midpoint first second) third) * 4 =
        Quadrance.quadrance (Affine.midpoint second third) first * 4 +
          Quadrance.quadrance (Affine.midpoint first third) second * 4 +
          Quadrance.quadrance (Affine.midpoint first second) third * 4 := by ring1
    _ = (2 * Quadrance.quadrance second first + 2 * Quadrance.quadrance third first -
          Quadrance.quadrance second third) +
        (2 * Quadrance.quadrance first second + 2 * Quadrance.quadrance third second -
          Quadrance.quadrance first third) +
        (2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
          Quadrance.quadrance first second) := by
      rw [median_quadrance_cleared second third first twoNonzero,
        median_quadrance_cleared first third second twoNonzero,
        median_quadrance_cleared first second third twoNonzero]
    _ = 3 * (Quadrance.quadrance second third + Quadrance.quadrance first third +
        Quadrance.quadrance first second) := by
      rw [Quadrance.quadrance_symm second first, Quadrance.quadrance_symm third first,
        Quadrance.quadrance_symm third second]
      ring1

/-- The sum of the three median quadrances is three quarters of the sum of the side quadrances.

The field has nonzero two, so division by four is valid. -/
theorem exercise_11_7
    (first second third : Geometry.Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance first (Affine.midpoint second third) +
        Quadrance.quadrance second (Affine.midpoint first third) +
        Quadrance.quadrance third (Affine.midpoint first second) =
      (3 * (Quadrance.quadrance second third + Quadrance.quadrance first third +
        Quadrance.quadrance first second)) / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    (Quadrance.quadrance first (Affine.midpoint second third) +
          Quadrance.quadrance second (Affine.midpoint first third) +
          Quadrance.quadrance third (Affine.midpoint first second)) * 4 =
        3 * (Quadrance.quadrance second third + Quadrance.quadrance first third +
          Quadrance.quadrance first second) :=
      exercise_11_7_cleared first second third twoNonzero
    _ = ((3 * (Quadrance.quadrance second third + Quadrance.quadrance first third +
        Quadrance.quadrance first second)) / 4) * 4 :=
      (ExplicitField.div_mul_cancel _ fourNonzero).symm
end Purelib.Geometry.Triangles.Median.Quadrance

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5 triangle exercises

The centroid calculation is reduced to two finite affine-scaling identities.
All divisions retain explicit characteristic-two and characteristic-three
certificates.
-/

namespace Purelib.Geometry.Triangles.Median.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Exercise 5.2: the centroid divides a median in the exact quadrance ratios `4/9` and `1/9`, and hence the
vertex--centroid quadrance is four times the centroid--midpoint quadrance. -/
theorem centroid_quadrance_ratios
    (first second third : Geometry.Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    let oppositeMidpoint := Affine.midpoint second third
    let centroid := Geometry.centroidPoint first second third
    Quadrance.quadrance first centroid =
        4 * Quadrance.quadrance first oppositeMidpoint / 9 ∧
      Quadrance.quadrance centroid oppositeMidpoint =
        Quadrance.quadrance first oppositeMidpoint / 9 ∧
      Quadrance.quadrance first centroid =
        4 * Quadrance.quadrance centroid oppositeMidpoint := by
  dsimp only
  have threeCancel : (3 : K) * (3 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 3 threeNonzero
  have nineNonzero : (9 : K) ≠ 0 := by
    intro nineZero
    apply (ExplicitField.mul_ne_zero threeNonzero threeNonzero)
    calc
      (3 : K) * 3 = 9 := by ring1
      _ = 0 := nineZero
  have nineCancel : (9 : K) * (9 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 9 nineNonzero
  have inverseSquare : ((3 : K)⁻¹) ^ 2 = (9 : K)⁻¹ := by
    calc
      ((3 : K)⁻¹) ^ 2 =
          ((3 : K)⁻¹) ^ 2 * (9 * (9 : K)⁻¹) := by
            rw [nineCancel]
            ring1
      _ = (3 * (3 : K)⁻¹) ^ 2 * (9 : K)⁻¹ := by ring1
      _ = (9 : K)⁻¹ := by rw [threeCancel]; ring1
  have weightsSum : (1 : K) / 3 + 2 / 3 = 1 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 * (3 : K)⁻¹ + 2 * (3 : K)⁻¹ =
          3 * (3 : K)⁻¹ := by ring1
      _ = 1 := threeCancel
  have centroidFormula := Geometry.centroidPoint_eq_median_affineCombination
    first second third twoNonzero
  have firstScaled :
      Quadrance.quadrance first (Geometry.centroidPoint first second third) =
        ((2 : K) / 3) ^ 2 * Quadrance.quadrance first (Affine.midpoint second third) := by
    rw [centroidFormula]
    exact Quadrance.quadrance_affineCombination_left first (Affine.midpoint second third)
      ((1 : K) / 3) (2 / 3) weightsSum
  have secondScaled :
      Quadrance.quadrance (Geometry.centroidPoint first second third) (Affine.midpoint second third) =
        ((1 : K) / 3) ^ 2 * Quadrance.quadrance first (Affine.midpoint second third) := by
    rw [centroidFormula]
    exact Quadrance.quadrance_affineCombination_right first (Affine.midpoint second third)
      ((1 : K) / 3) (2 / 3) weightsSum
  have fourNinths : ((2 : K) / 3) ^ 2 = 4 / 9 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (2 * (3 : K)⁻¹) ^ 2 = 4 * ((3 : K)⁻¹) ^ 2 := by ring1
      _ = 4 * (9 : K)⁻¹ := by rw [inverseSquare]
  have oneNinth : ((1 : K) / 3) ^ 2 = 1 / 9 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (1 * (3 : K)⁻¹) ^ 2 = 1 * ((3 : K)⁻¹) ^ 2 := by ring1
      _ = 1 * (9 : K)⁻¹ := by rw [inverseSquare]
  have firstResult :
      Quadrance.quadrance first (Geometry.centroidPoint first second third) =
        4 * Quadrance.quadrance first (Affine.midpoint second third) / 9 := by
    calc
      Quadrance.quadrance first (Geometry.centroidPoint first second third) =
          ((2 : K) / 3) ^ 2 *
            Quadrance.quadrance first (Affine.midpoint second third) := firstScaled
      _ = 4 * Quadrance.quadrance first (Affine.midpoint second third) / 9 := by
        rw [fourNinths]
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  have secondResult :
      Quadrance.quadrance (Geometry.centroidPoint first second third) (Affine.midpoint second third) =
        Quadrance.quadrance first (Affine.midpoint second third) / 9 := by
    calc
      Quadrance.quadrance (Geometry.centroidPoint first second third) (Affine.midpoint second third) =
          ((1 : K) / 3) ^ 2 *
            Quadrance.quadrance first (Affine.midpoint second third) := secondScaled
      _ = Quadrance.quadrance first (Affine.midpoint second third) / 9 := by
        rw [oneNinth]
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  exact ⟨firstResult, secondResult,
    firstResult.trans (by
      rw [secondResult]
      simp only [ExplicitField.div_eq_mul_inv]
      ring1)⟩

end Purelib.Geometry.Triangles.Median.Quadrance

end

end
