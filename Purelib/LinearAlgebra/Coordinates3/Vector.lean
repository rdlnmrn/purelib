module

import Purelib.Algebra.Field.Characteristic.Nonzero

import Purelib.Algebra.Field.Ratio
public import Purelib.Algebra.Field.ExplicitField
-- Exposed coordinate negation retains this original subtraction parent.
public import Purelib.Algebra.Group.Negation
-- Public scalar numerals retain their explicit successor certificates.
public import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
@[expose] public section

set_option genInjectivity false in
/-- A displayed row vector `(t,r,s)` in three-dimensional space.

The three retained scalar coordinates keep their original order and carrier.
Constructor certificates identify those same coordinates individually, without
changing the displayed vector or its executable coordinate operations. -/
@[ext]
structure Vector (K : Type*) where
  /-- The retained `t` coordinate of the displayed vector. -/ t : K
  /-- The retained `r` coordinate of the displayed vector. -/ r : K
  /-- The retained `s` coordinate of the displayed vector. -/ s : K
deriving DecidableEq

constructive_injectivity Vector

end
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Coordinatewise vector addition. -/
@[expose] def add (left right : Vector K) : Vector K :=
  ⟨left.t + right.t, left.r + right.r, left.s + right.s⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The finite Cartesian cross product. -/
@[expose] def cross (left right : Vector K) : Vector K :=
  ⟨left.r * right.s - right.r * left.s,
    left.s * right.t - right.s * left.t,
    left.t * right.r - right.t * left.r⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The displayed determinant with the three vectors as rows. -/
@[expose] def determinant (first second third : Vector K) : K :=
  first.t * (second.r * third.s - second.s * third.r) -
    first.r * (second.t * third.s - second.s * third.t) +
      first.s * (second.t * third.r - second.r * third.t)
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Equal cross products give equal ratios when both denominators are nonzero. -/
private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A quotient with nonzero denominator can vanish only when its numerator vanishes. -/
private theorem div_eq_zero [DecidableEq K]
    (numerator denominator : K) (denominatorNonzero : denominator ≠ 0)
    (quotientZero : numerator / denominator = 0) : numerator = 0 := by
  by_cases numeratorZero : numerator = 0
  · exact numeratorZero
  · exact (ExplicitField.div_ne_zero numeratorZero denominatorNonzero
      quotientZero).elim
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The finite Cartesian dot product. -/
@[expose] def dot (left right : Vector K) : K :=
  left.t * right.t + left.r * right.r + left.s * right.s
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Coordinatewise vector negation. -/
@[expose] def neg (vector : Vector K) : Vector K :=
  ⟨-vector.t, -vector.r, -vector.s⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Subtracting a ratio from one subtracts its numerator from the nonzero denominator. -/
private theorem one_sub_div (numerator denominator : K)
    (denominatorNonzero : denominator ≠ 0) :
    1 - numerator / denominator =
      (denominator - numerator) / denominator := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - numerator * denominator⁻¹ =
        denominator * denominator⁻¹ -
          numerator * denominator⁻¹ := by rw [cancel]
    _ = (denominator - numerator) * denominator⁻¹ := by ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Left scalar multiplication of a displayed vector. -/
@[expose] def scale (scalar : K) (vector : Vector K) : Vector K :=
  ⟨scalar * vector.t, scalar * vector.r, scalar * vector.s⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- An element whose square vanishes is zero in the explicit field. -/
private theorem square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Coordinatewise vector subtraction. -/
@[expose] def sub (left right : Vector K) : Vector K :=
  ⟨left.t - right.t, left.r - right.r, left.s - right.s⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The zero vector. -/
@[expose] def zero : Vector K := ⟨0, 0, 0⟩
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- One displayed vector is a nonzero scalar multiple of the other.

The witness retains the scalar and its nonvanishing proof; both zero vectors satisfy this relation. -/
@[expose] def Parallel (left right : Vector K) : Prop :=
  ∃ scalar : K, scalar ≠ 0 ∧ left = scale scalar right
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Two vectors are perpendicular precisely when their dot product vanishes. -/
@[expose] def Perpendicular (left right : Vector K) : Prop := dot left right = 0
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `r` coordinate of vector add is the sum of the corresponding input coordinates. -/
@[simp] theorem add_r (left right : Vector K) :
    (add left right).r = left.r + right.r := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `s` coordinate of vector add is the sum of the corresponding input coordinates. -/
@[simp] theorem add_s (left right : Vector K) :
    (add left right).s = left.s + right.s := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `t` coordinate of vector add is the sum of the corresponding input coordinates. -/
@[simp] theorem add_t (left right : Vector K) :
    (add left right).t = left.t + right.t := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in
/-- Adding the zero vector on the right preserves a displayed vector. -/
@[simp] theorem add_zero (vector : Vector K) : add vector zero = vector := by
  apply Vector3.ext <;> exact _root_.add_zero _
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Theorem 5.3: the Binet--Cauchy identity in displayed coordinates. -/
theorem binet_cauchy (first second third fourth : Vector K) :
    dot (cross first second) (cross third fourth) =
      dot first third * dot second fourth -
        dot first fourth * dot second third := by
  unfold dot cross
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The cross product distributes over addition in its first argument. -/
@[simp] theorem cross_add_left (first second third : Vector K) :
    cross (add first second) third =
      add (cross first third) (cross second third) := by
  ext <;> unfold cross add <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The cross product distributes over addition in its second argument. -/
@[simp] theorem cross_add_right (first second third : Vector K) :
    cross first (add second third) =
      add (cross first second) (cross first third) := by
  ext <;> unfold cross add <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Exchanging cross-product arguments negates the resulting vector. -/
theorem cross_anticomm (left right : Vector K) :
    cross left right = neg (cross right left) := by
  ext <;> unfold cross neg <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The scalar triple product vanishes when its third argument repeats the
first cross-product argument. -/
@[simp] theorem cross_dot_left (left right : Vector K) :
    dot (cross left right) left = 0 := by
  unfold dot cross
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The scalar triple product vanishes when its third argument repeats the
second cross-product argument. -/
@[simp] theorem cross_dot_right (left right : Vector K) :
    dot (cross left right) right = 0 := by
  unfold dot cross
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A scalar in the first cross-product argument factors out. -/
@[simp] theorem cross_scale_left (scalar : K) (left right : Vector K) :
    cross (scale scalar left) right = scale scalar (cross left right) := by
  ext <;> unfold cross scale <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A scalar in the second cross-product argument factors out. -/
@[simp] theorem cross_scale_right (scalar : K) (left right : Vector K) :
    cross left (scale scalar right) = scale scalar (cross left right) := by
  ext <;> unfold cross scale <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The cross product with the zero vector on the left is zero. -/
@[simp] theorem cross_zero_left (vector : Vector K) : cross zero vector = zero := by
  ext <;> unfold cross zero <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The cross product with the zero vector on the right is zero. -/
@[simp] theorem cross_zero_right (vector : Vector K) : cross vector zero = zero := by
  ext <;> unfold cross zero <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The displayed determinant is additive in its third row. -/
theorem determinant_add_third (first second third fourth : Vector K) :
    determinant first second (add third fourth) =
      determinant first second third + determinant first second fourth := by
  unfold determinant add
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Negating the first row negates the displayed determinant. -/
theorem determinant_neg_first (first second third : Vector K) :
    determinant (neg first) second third =
      -determinant first second third := by
  unfold determinant neg
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Repeating the second row makes the displayed determinant vanish. -/
@[simp] theorem determinant_repeat_second (first second : Vector K) :
    determinant first second second = 0 := by
  unfold determinant
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The displayed determinant is homogeneous in its third row. -/
theorem determinant_scale_third (scalar : K)
    (first second third : Vector K) :
    determinant first second (scale scalar third) =
      scalar * determinant first second third := by
  unfold determinant scale
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The dot product distributes over addition in its first argument. -/
@[simp] theorem dot_add_left (first second third : Vector K) :
    dot (add first second) third = dot first third + dot second third := by
  unfold dot add
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The dot product distributes over addition in its second argument. -/
@[simp] theorem dot_add_right (first second third : Vector K) :
    dot first (add second third) = dot first second + dot first third := by
  unfold dot add
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Exchanging the two displayed vectors preserves their dot product. -/
theorem dot_comm (left right : Vector K) : dot left right = dot right left := by
  unfold dot
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Negating the first vector negates its dot product. -/
@[simp] theorem dot_neg_left (left right : Vector K) :
    dot (neg left) right = -dot left right := by
  unfold dot neg
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Negating the second vector negates its dot product. -/
@[simp] theorem dot_neg_right (left right : Vector K) :
    dot left (neg right) = -dot left right := by
  unfold dot neg
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A scalar in the first dot-product argument factors out. -/
@[simp] theorem dot_scale_left (scalar : K) (left right : Vector K) :
    dot (scale scalar left) right = scalar * dot left right := by
  unfold dot scale
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A scalar in the second dot-product argument factors out. -/
@[simp] theorem dot_scale_right (scalar : K) (left right : Vector K) :
    dot left (scale scalar right) = scalar * dot left right := by
  unfold dot scale
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The dot product with the zero vector on the left vanishes. -/
@[simp] theorem dot_zero_left (vector : Vector K) : dot zero vector = 0 := by
  unfold dot zero
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `r` coordinate of vector neg is the negation of the original coordinate. -/
@[simp] theorem neg_r (vector : Vector K) :
    (neg vector).r = -vector.r := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `s` coordinate of vector neg is the negation of the original coordinate. -/
@[simp] theorem neg_s (vector : Vector K) :
    (neg vector).s = -vector.s := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `t` coordinate of vector neg is the negation of the original coordinate. -/
@[simp] theorem neg_t (vector : Vector K) :
    (neg vector).t = -vector.t := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in
/-- Negating the zero vector preserves it. -/
@[simp] theorem neg_zero : neg (zero : Vector K) = zero := by
  apply Vector3.ext <;> exact _root_.neg_zero

/-- Negating a vector twice recovers its original coordinates. -/
theorem neg_neg (vector : Vector K) : neg (neg vector) = vector := by
  apply Vector.ext <;> exact _root_.neg_neg _
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Definition 1: the quadrance `Q(v)=v·v`. -/
@[expose] def quadrance (vector : Vector K) : K := dot vector vector
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Theorem 5.1: the scalar triple product is the displayed determinant. -/
theorem scalar_triple_product (first second third : Vector K) :
    dot (cross first second) third = determinant first second third := by
  unfold dot cross determinant
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scalar multiplication distributes over displayed vector addition. -/
theorem scale_add (scalar : K) (left right : Vector K) :
    scale scalar (add left right) =
      add (scale scalar left) (scale scalar right) := by
  ext <;> unfold scale add <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `r` coordinate of vector scale is the scalar times the original coordinate. -/
@[simp] theorem scale_r (scalar : K) (vector : Vector K) :
    (scale scalar vector).r = scalar * vector.r := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `s` coordinate of vector scale is the scalar times the original coordinate. -/
@[simp] theorem scale_s (scalar : K) (vector : Vector K) :
    (scale scalar vector).s = scalar * vector.s := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Two successive vector scalings multiply their scalars. -/
theorem scale_scale (first second : K) (vector : Vector K) :
    scale first (scale second vector) = scale (first * second) vector := by
  ext <;> unfold scale <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scalar multiplication distributes over displayed vector subtraction. -/
theorem scale_sub (scalar : K) (left right : Vector K) :
    scale scalar (sub left right) =
      sub (scale scalar left) (scale scalar right) := by
  ext <;> unfold scale sub <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `t` coordinate of vector scale is the scalar times the original coordinate. -/
@[simp] theorem scale_t (scalar : K) (vector : Vector K) :
    (scale scalar vector).t = scalar * vector.t := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `r` coordinate of vector sub is the difference of the corresponding input coordinates. -/
@[simp] theorem sub_r (left right : Vector K) :
    (sub left right).r = left.r - right.r := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `s` coordinate of vector sub is the difference of the corresponding input coordinates. -/
@[simp] theorem sub_s (left right : Vector K) :
    (sub left right).s = left.s - right.s := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `t` coordinate of vector sub is the difference of the corresponding input coordinates. -/
@[simp] theorem sub_t (left right : Vector K) :
    (sub left right).t = left.t - right.t := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Theorem 5.2: the vector triple-product identity. -/
theorem vector_triple_product (first second third : Vector K) :
    cross first (cross second third) =
      sub (scale (dot first third) second)
        (scale (dot first second) third) := by
  ext <;> unfold cross sub scale dot <;> ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in
/-- Adding the zero vector on the left preserves a displayed vector. -/
@[simp] theorem zero_add (vector : Vector K) : add zero vector = vector := by
  apply Vector3.ext <;> exact _root_.zero_add _
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `r` coordinate of vector zero is the zero. -/
@[simp] theorem zero_r : (zero : Vector K).r = 0 := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `s` coordinate of vector zero is the zero. -/
@[simp] theorem zero_s : (zero : Vector K).s = 0 := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The `t` coordinate of vector zero is the zero. -/
@[simp] theorem zero_t : (zero : Vector K).t = 0 := rfl
end Vector
end Purelib.LinearAlgebra.Coordinates3

end
section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- A vector is null precisely when its quadrance vanishes. -/
@[expose] def IsNull (vector : Vector K) : Prop := quadrance vector = 0
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The dot product with the zero vector on the right vanishes. -/
@[simp] theorem dot_zero_right (vector : Vector K) : dot vector zero = 0 := by
  rw [dot_comm, dot_zero_left]
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Theorem 6: Lagrange's identity. -/
theorem lagrange (left right : Vector K) :
    dot left right ^ 2 + quadrance (cross left right) =
      quadrance left * quadrance right := by
  unfold quadrance dot cross
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scaling a displayed vector by one preserves it.

Left-unit multiplication recovers each of the three original coordinates.
The coordinate equalities identify the displayed vector directly. -/
@[simp] theorem one_scale (vector : Vector K) : scale 1 vector = vector := by
  apply Vector.ext
  · exact one_mul vector.t
  · exact one_mul vector.r
  · exact one_mul vector.s
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Quadrance of a displayed vector sum. -/
theorem quadrance_add (left right : Vector K) :
    quadrance (add left right) =
      quadrance left + 2 * dot left right + quadrance right := by
  unfold quadrance dot add
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Negating a displayed vector preserves its quadrance. -/
@[simp] theorem quadrance_neg (vector : Vector K) :
    quadrance (neg vector) = quadrance vector := by
  unfold quadrance dot neg
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scaling a vector multiplies its quadrance by the square of the scalar. -/
theorem quadrance_scale (scalar : K) (vector : Vector K) :
    quadrance (scale scalar vector) = scalar ^ 2 * quadrance vector := by
  unfold quadrance dot scale
  ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The zero vector has zero quadrance. -/
@[simp] theorem quadrance_zero : quadrance (zero : Vector K) = 0 := by
  unfold quadrance
  rw [dot_zero_left]
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Every scalar multiple of the zero vector is zero.

Right-zero multiplication makes each of the three displayed coordinates zero.
These coordinate equalities identify the original zero vector directly. -/
@[simp] theorem scale_zero (scalar : K) : scale scalar zero = zero := by
  apply Vector.ext
  · exact mul_zero scalar
  · exact mul_zero scalar
  · exact mul_zero scalar
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Definition 4: spread of two non-null displayed directions.  The
non-nullness certificates are retained in the data interface so callers
cannot form the paper's geometric quantity at a forbidden denominator. -/
@[expose] def spread (left right : Vector K)
    (_leftNonNull : quadrance left ≠ 0)
    (_rightNonNull : quadrance right ≠ 0) : K :=
  1 - dot left right ^ 2 / (quadrance left * quadrance right)
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scaling any displayed vector by zero gives the zero vector.

Left-zero multiplication makes each of the three displayed coordinates zero.
These coordinate equalities identify the original zero vector directly. -/
@[simp] theorem zero_scale (vector : Vector K) : scale 0 vector = zero := by
  apply Vector.ext
  · exact zero_mul vector.t
  · exact zero_mul vector.r
  · exact zero_mul vector.s
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Three-dimensional Pythagoras for two explicitly perpendicular vectors. -/
theorem quadrance_add_of_perpendicular (first second : Vector K)
    (perpendicular : Perpendicular first second) :
    quadrance (add first second) = quadrance first + quadrance second := by
  rw [quadrance_add, perpendicular]
  ring1

end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Scaling a non-null vector by a nonzero scalar preserves non-nullness. -/
theorem quadrance_scale_ne_zero (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (vectorNonNull : quadrance vector ≠ 0) :
    quadrance (scale scalar vector) ≠ 0 := by
  rw [quadrance_scale]
  exact ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using
        ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
    vectorNonNull
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- The consequence of Theorem 6 printed after Lagrange's identity: spread
is the quadrance of the cross product divided by the two quadrances. -/
theorem spread_eq_cross_quadrance (left right : Vector K)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left right leftNonNull rightNonNull =
      quadrance (cross left right) /
        (quadrance left * quadrance right) := by
  have denominatorNonzero : quadrance left * quadrance right ≠ 0 :=
    ExplicitField.mul_ne_zero leftNonNull rightNonNull
  unfold spread
  rw [one_sub_div _ _ denominatorNonzero]
  congr 1
  have identity := lagrange left right
  calc
    quadrance left * quadrance right - dot left right ^ 2 =
        dot left right ^ 2 + quadrance (cross left right) -
          dot left right ^ 2 := by rw [identity]
    _ = quadrance (cross left right) := by ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- For non-null vectors over a computational field, spread one is exactly
perpendicularity. -/
theorem spread_eq_one_iff_perpendicular [DecidableEq K]
    (left right : Vector K)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left right leftNonNull rightNonNull = 1 ↔
      Perpendicular left right := by
  have denominatorNonzero : quadrance left * quadrance right ≠ 0 :=
    ExplicitField.mul_ne_zero leftNonNull rightNonNull
  constructor
  · intro spreadOne
    have quotientZero :
        dot left right ^ 2 /
          (quadrance left * quadrance right) = 0 := by
      unfold spread at spreadOne
      calc
        dot left right ^ 2 / (quadrance left * quadrance right) =
            1 - (1 - dot left right ^ 2 /
              (quadrance left * quadrance right)) := by ring1
        _ = 0 := by rw [spreadOne]; ring1
    exact square_eq_zero _
      (div_eq_zero _ _ denominatorNonzero quotientZero)
  · intro perpendicular
    unfold Perpendicular at perpendicular
    unfold spread
    rw [perpendicular]
    simp only [zero_pow (by decide : 2 ≠ 0), ExplicitField.zero_div]
    ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Spread is unchanged by a nonzero rescaling of its first direction. -/
theorem spread_scale_left (scalar : K) (left right : Vector K)
    (scalarNonzero : scalar ≠ 0)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread (scale scalar left) right
        (quadrance_scale_ne_zero scalar left scalarNonzero leftNonNull)
        rightNonNull =
      spread left right leftNonNull rightNonNull := open Purelib in by
  unfold spread
  congr 1
  rw [dot_scale_left, quadrance_scale]
  apply Algebra.Field.Ratio.ratio_eq_of_cross_product
  · exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (by
          simpa only [pow_two] using
            ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
        leftNonNull)
      rightNonNull
  · exact ExplicitField.mul_ne_zero leftNonNull rightNonNull
  · ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3
variable {K : Type*} [ExplicitField K]
namespace Vector

/-- Spread is unchanged by a nonzero rescaling of its second direction. -/
theorem spread_scale_right (scalar : K) (left right : Vector K)
    (scalarNonzero : scalar ≠ 0)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left (scale scalar right) leftNonNull
        (quadrance_scale_ne_zero scalar right scalarNonzero rightNonNull) =
      spread left right leftNonNull rightNonNull := open Purelib in by
  unfold spread
  congr 1
  rw [dot_scale_right, quadrance_scale]
  apply Algebra.Field.Ratio.ratio_eq_of_cross_product
  · exact ExplicitField.mul_ne_zero leftNonNull
      (ExplicitField.mul_ne_zero
        (by
          simpa only [pow_two] using
            ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
        rightNonNull)
  · exact ExplicitField.mul_ne_zero leftNonNull rightNonNull
  · ring1
end Vector
end Purelib.LinearAlgebra.Coordinates3

end

section
public section
namespace Purelib.LinearAlgebra.Coordinates3.Vector

variable {K : Type*} [ExplicitField K]

/-- Cancel a nonzero common scalar from equality of displayed vectors. -/
public theorem
  eq_of_scale_eq_scale
  {factor : K}
    (factorNonzero : factor ≠ 0) {left right : Vector K}
    (scaled : scale factor left = scale factor right) :
    left = right := by
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel factor factorNonzero
  apply Coordinates3.Vector.ext
  · have coordinate := congrArg Coordinates3.Vector.t scaled
    dsimp only [scale] at coordinate
    calc
      left.t = (factor⁻¹ * factor) * left.t := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.t) := by ring1
      _ = factor⁻¹ * (factor * right.t) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.t := by ring1
      _ = right.t := by rw [reverseCancel, one_mul]
  · have coordinate := congrArg Coordinates3.Vector.r scaled
    dsimp only [scale] at coordinate
    calc
      left.r = (factor⁻¹ * factor) * left.r := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.r) := by ring1
      _ = factor⁻¹ * (factor * right.r) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.r := by ring1
      _ = right.r := by rw [reverseCancel, one_mul]
  · have coordinate := congrArg Coordinates3.Vector.s scaled
    dsimp only [scale] at coordinate
    calc
      left.s = (factor⁻¹ * factor) * left.s := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.s) := by ring1
      _ = factor⁻¹ * (factor * right.s) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.s := by ring1
      _ = right.s := by rw [reverseCancel, one_mul]

end Purelib.LinearAlgebra.Coordinates3.Vector
end

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
namespace Purelib.LinearAlgebra.Coordinates3.Vector
variable {K : Type*} [ExplicitField K]

/-- A vector equal to its own negative is zero when two is nonzero. -/
public theorem eq_zero_of_eq_neg (vector :
  Vector K)
    (twoNonzero : (2 : K) ≠ 0)
    (selfNegative : vector = neg vector) :
    vector = zero := by
  have tRelation : vector.t = -vector.t := by
    simpa only [neg_t] using congrArg Coordinates3.Vector.t selfNegative
  have rRelation : vector.r = -vector.r := by
    simpa only [neg_r] using congrArg Coordinates3.Vector.r selfNegative
  have sRelation : vector.s = -vector.s := by
    simpa only [neg_s] using congrArg Coordinates3.Vector.s selfNegative
  apply Coordinates3.Vector.ext
  · apply (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) {value : K} (twiceZero :
    2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
    twiceZero : value = 0)) (K := K) twoNonzero
    calc
      2 * vector.t = vector.t + vector.t := by ring1
      _ = -vector.t + vector.t :=
        congrArg (fun value => value + vector.t) tRelation
      _ = 0 := neg_add_cancel vector.t
  · apply (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) {value : K} (twiceZero :
    2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
    twiceZero : value = 0)) (K := K) twoNonzero
    calc
      2 * vector.r = vector.r + vector.r := by ring1
      _ = -vector.r + vector.r :=
        congrArg (fun value => value + vector.r) rRelation
      _ = 0 := neg_add_cancel vector.r
  · apply (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) {value : K} (twiceZero :
    2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
    twiceZero : value = 0)) (K := K) twoNonzero
    calc
      2 * vector.s = vector.s + vector.s := by ring1
      _ = -vector.s + vector.s :=
        congrArg (fun value => value + vector.s) sRelation
      _ = 0 := neg_add_cancel vector.s

end Purelib.LinearAlgebra.Coordinates3.Vector
end
