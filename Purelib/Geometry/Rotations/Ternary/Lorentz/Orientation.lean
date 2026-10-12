module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.Projective
import Purelib.Geometry.Rotations.Ternary.Lorentz.Anchor
public import Purelib.Geometry.Quadratic.Ternary.Lorentz.Ordered
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.LinearAlgebra.Coordinates3.Ray
import Purelib.Tactic.Ring

/-!
# Orientation of time-first Lorentz rotations

The original anchor vector changes sign under inversion. The determinant
of an axis, a perpendicular vector and its rotated image measures their
ordered frame, with the Lorentz quadrance signs retained explicitly.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- Inverting a Lorentz rotation negates the vector read from its original computed anchor. -/
theorem rotationAnchorVector_inverse (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) :
    rotationAnchorVector oneNonzero (Basic.TernaryForm.SpecialOrthogonal.inverse rotation)
        (by rw [rotation.anchorDenominator_inverse]; exact defined) =
      Vector3.neg (rotationAnchorVector oneNonzero rotation defined) := by
  unfold rotationAnchorVector
  rw [rotation.anchor_inverse defined]
  ext <;> unfold Quadratic.Ternary.Lorentz.anchorVector Matrix3.neg Vector3.neg <;> ring1

/-- Inversion takes every nonzero original Lorentz anchor to its distinct opposite ray.

The recovered anchor vectors differ by negation. Positive ray equivalence
therefore distinguishes the inverse pair for timelike, spacelike and null
anchors without introducing a causal-type-dependent determinant criterion.
-/
theorem rotationAnchorVector_inverse_distinct_ray {L : Type*} [RayOrderedExplicitField L]
    (oneNonzero : (1 : L) ≠ 0) (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0)
    (anchorNonzero : rotationAnchorVector oneNonzero rotation defined ≠ Vector3.zero) :
    ¬ Vector3.RayEquivalent (rotationAnchorVector oneNonzero rotation defined)
      (rotationAnchorVector oneNonzero (Basic.TernaryForm.SpecialOrthogonal.inverse rotation)
        (by rw [rotation.anchorDenominator_inverse]; exact defined)) := by
  rw [rotationAnchorVector_inverse oneNonzero rotation defined]
  exact Vector3.not_rayEquivalent_neg _ anchorNonzero

/-- A Lorentz cap acts on a perpendicular vector by its scalar and signed cross components.

The vector's projection onto the axis vanishes. Its anchor square therefore
acts by minus the axis quadrance, giving the exact reduced action formula.
-/
theorem rowMul_cap_of_perpendicular (axis vector : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis) :
    Matrix3.rowMul vector (cap oneNonzero axis defined) =
      Vector3.scale (capDenominator oneNonzero axis)⁻¹
        (Vector3.add (Vector3.scale (1 - (Form.lorentz oneNonzero).quadrance axis) vector)
          (Vector3.scale 2 (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector))) := by
  rw [cap_quadratic, Matrix3.rowMul_add, Matrix3.rowMul_identity, Matrix3.rowMul_scale,
    Matrix3.rowMul_add, Quadratic.Ternary.Lorentz.rowMul_anchor,
    Quadratic.Ternary.Lorentz.anchor_square, Matrix3.rowMul_sub, Matrix3.rowMul_outer,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    ← (Form.lorentz oneNonzero).bilinear_eq_dot_dual, perpendicular]
  have cancellation := ExplicitField.mul_inv_cancel (capDenominator oneNonzero axis) defined
  have coefficient : 1 - (2 / capDenominator oneNonzero axis) *
      (Form.lorentz oneNonzero).quadrance axis =
      (capDenominator oneNonzero axis)⁻¹ * (1 - (Form.lorentz oneNonzero).quadrance axis) := by
    calc
      _ = capDenominator oneNonzero axis * (capDenominator oneNonzero axis)⁻¹ -
          (2 / capDenominator oneNonzero axis) * (Form.lorentz oneNonzero).quadrance axis := by
        rw [cancellation]
      _ = _ := by
        unfold capDenominator
        rw [ExplicitField.div_eq_mul_inv]
        ring1
  have scalar (x y z : K) : x + (2 / capDenominator oneNonzero axis) *
      (y + (0 * z - (Form.lorentz oneNonzero).quadrance axis * x)) =
      (capDenominator oneNonzero axis)⁻¹ *
        ((1 - (Form.lorentz oneNonzero).quadrance axis) * x + 2 * y) := by
    calc
      _ = (1 - (2 / capDenominator oneNonzero axis) *
          (Form.lorentz oneNonzero).quadrance axis) * x +
          (2 / capDenominator oneNonzero axis) * y := by ring1
      _ = _ := by rw [coefficient, ExplicitField.div_eq_mul_inv]; ring1
  ext <;> unfold Vector3.add Vector3.sub Vector3.scale <;> exact scalar _ _ _

/-- The Lorentz cap frame determinant retains the signed axis and test quadrances.

The scalar component of the rotated perpendicular vector repeats the
second row. The cross component contributes minus its quadrance through
the signed scalar triple product and the Lorentz Lagrange identity.
-/
theorem determinant_cap_frame (axis vector : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis) :
    Vector3.determinant axis vector (Matrix3.rowMul vector (cap oneNonzero axis defined)) =
      (-2 * (Form.lorentz oneNonzero).quadrance axis / capDenominator oneNonzero axis) *
        (Form.lorentz oneNonzero).quadrance vector := by
  have axisPerpendicular : (Form.lorentz oneNonzero).bilinear axis vector = 0 := by
    rw [(Form.lorentz oneNonzero).bilinear_comm]
    exact perpendicular
  have crossQuadrance : (Form.lorentz oneNonzero).quadrance
      (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) =
        (Form.lorentz oneNonzero).quadrance axis * (Form.lorentz oneNonzero).quadrance vector := by
    have lagrange := Quadratic.Ternary.Lorentz.lagrange oneNonzero axis vector
    rw [axisPerpendicular] at lagrange
    calc
      _ = 0 ^ 2 + (Form.lorentz oneNonzero).quadrance
        (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) := by ring1
      _ = _ := lagrange
  have triple : Vector3.determinant axis vector (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) =
      -(Form.lorentz oneNonzero).quadrance (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) := by
    have pairing := Quadratic.Ternary.Lorentz.scalar_triple_product oneNonzero axis vector
      (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector)
    change (Form.lorentz oneNonzero).quadrance (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) =
      -Vector3.determinant axis vector (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector) at pairing
    calc
      _ = -(-Vector3.determinant axis vector (Quadratic.Ternary.Lorentz.cross oneNonzero axis vector)) := by ring1
      _ = _ := congrArg (fun scalar : K => -scalar) pairing.symm
  rw [rowMul_cap_of_perpendicular oneNonzero axis vector defined perpendicular,
    Vector3.determinant_scale_third, Vector3.determinant_add_third,
    Vector3.determinant_scale_third, Vector3.determinant_scale_third,
    Vector3.determinant_repeat_second, triple, crossQuadrance]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- Every perpendicular Lorentz cap frame has zero determinant when the original axis is null. -/
theorem determinant_cap_frame_of_null (axis vector : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis)
    (null : (Form.lorentz oneNonzero).quadrance axis = 0) :
    Vector3.determinant axis vector (Matrix3.rowMul vector (cap oneNonzero axis defined)) = 0 := by
  rw [determinant_cap_frame oneNonzero axis vector defined perpendicular, null]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- Every nonzero perpendicular frame of a timelike Lorentz cap has positive determinant.

The original perpendicular test vector has positive negative quadrance.
The frame determinant is a product of this value, the positive axis
quadrance, positive two and the inverse of the positive cap denominator.
-/
theorem determinant_cap_frame_pos_of_timelike {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (axis vector : Vector3 F)
    (defined : capDenominator oneNonzero axis ≠ 0)
    (positive : 0 < (Form.lorentz oneNonzero).quadrance axis)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis)
    (nonzero : vector ≠ Vector3.zero) :
    0 < Vector3.determinant axis vector (Matrix3.rowMul vector (cap oneNonzero axis defined)) := by
  have testPositive := Quadratic.Ternary.Lorentz.neg_quadrance_pos_of_perpendicular_timelike
    oneNonzero axis vector positive perpendicular nonzero
  have denominatorPositive : 0 < capDenominator oneNonzero axis :=
    OrderedExplicitField.add_pos_direct OrderedExplicitField.zero_lt_one_direct positive
  rw [determinant_cap_frame oneNonzero axis vector defined perpendicular]
  rw [show (-2 * (Form.lorentz oneNonzero).quadrance axis / capDenominator oneNonzero axis) *
      (Form.lorentz oneNonzero).quadrance vector =
      (2 * (Form.lorentz oneNonzero).quadrance axis *
        (-(Form.lorentz oneNonzero).quadrance vector)) * (capDenominator oneNonzero axis)⁻¹ by
    rw [ExplicitField.div_eq_mul_inv]
    ring1]
  exact OrderedExplicitField.mul_pos_direct
    (OrderedExplicitField.mul_pos_direct
      (OrderedExplicitField.mul_pos_direct RayOrderedExplicitField.two_pos positive) testPositive)
    (OrderedExplicitField.inv_pos_direct denominatorPositive)

/-- A non-null source proportion has a strictly positive time-entry numerator over an ordered field.

Finite equality decisions locate a nonzero coordinate. Its positive
square remains positive after adding the other three squares; all four
zero coordinates contradict the retained norm certificate.
-/
theorem proportionTimeNumerator_pos {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (scalar : F) (vector : Vector3 F)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    0 < scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 := by
  letI : DecidableEq F := OrderedExplicitField.eq_decidable
  have positiveAt (base first second third : F) (nonzero : base ≠ 0) :
      0 < base ^ 2 + first ^ 2 + second ^ 2 + third ^ 2 :=
    RayOrderedExplicitField.add_square_pos
      (RayOrderedExplicitField.add_square_pos
        (RayOrderedExplicitField.add_square_pos (by
          simpa only [pow_two] using OrderedExplicitField.mul_self_pos_direct nonzero)))
  by_cases scalarZero : scalar = 0
  · by_cases timeZero : vector.t = 0
    · by_cases firstZero : vector.r = 0
      · by_cases secondZero : vector.s = 0
        · apply False.elim
          apply defined
          rw [Form.quadrance_lorentz, scalarZero, timeZero, firstZero, secondZero]
          ring1
        · rw [show scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 =
            vector.s ^ 2 + scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 by ring1]
          exact positiveAt vector.s scalar vector.t vector.r secondZero
      · rw [show scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 =
          vector.r ^ 2 + scalar ^ 2 + vector.t ^ 2 + vector.s ^ 2 by ring1]
        exact positiveAt vector.r scalar vector.t vector.s firstZero
    · rw [show scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 =
        vector.t ^ 2 + scalar ^ 2 + vector.r ^ 2 + vector.s ^ 2 by ring1]
      exact positiveAt vector.t scalar vector.r vector.s timeZero
  · exact positiveAt scalar vector.t vector.r vector.s scalarZero

/-- A source proportion rotation preserves time direction exactly when its retained norm is positive.

The time-entry numerator is positive for every non-null representative.
The explicit finite sign split of the denominator therefore determines
its time-entry sign, including the scalar-zero chart.
-/
theorem proportionRotation_time_pos_iff {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (scalar : F) (vector : Vector3 F)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    0 < (proportionRotation oneNonzero scalar vector defined).matrix.tt ↔
      0 < scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector := by
  rw [proportionRotation_timeEntry, ExplicitField.div_eq_mul_inv]
  have numeratorPositive := proportionTimeNumerator_pos oneNonzero scalar vector defined
  constructor
  · intro timePositive
    rcases RayOrderedExplicitField.sign_split_direct _ defined with normPositive | negativeNormPositive
    · exact normPositive
    · have negativeTimePositive := OrderedExplicitField.mul_pos_direct numeratorPositive
        (OrderedExplicitField.inv_pos_direct negativeNormPositive)
      rw [ExplicitField.inv_neg] at negativeTimePositive
      have negativeProduct :
          (scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2) *
            -(scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ =
          -((scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2) *
            (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹) := by ring1
      rw [negativeProduct] at negativeTimePositive
      exact False.elim (RayOrderedExplicitField.positive_neg_exclusive_direct timePositive negativeTimePositive)
  · intro normPositive
    exact OrderedExplicitField.mul_pos_direct numeratorPositive (OrderedExplicitField.inv_pos_direct normPositive)

/-- Products of two source proportion rotations with positive time entry have positive time entry.

The same retained input norms multiply to the output norm. Its positivity
is transported through the exact projective rotation multiplication law,
with no affine-chart restriction.
-/
theorem proportionRotation_mul_time_pos {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (leftScalar rightScalar : F) (leftVector rightVector : Vector3 F)
    (leftDefined : leftScalar ^ 2 + (Form.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (Form.lorentz oneNonzero).quadrance rightVector ≠ 0)
    (leftPositive : 0 < (proportionRotation oneNonzero leftScalar leftVector leftDefined).matrix.tt)
    (rightPositive : 0 < (proportionRotation oneNonzero rightScalar rightVector rightDefined).matrix.tt) :
    0 < (Basic.TernaryForm.SpecialOrthogonal.mul
      (proportionRotation oneNonzero leftScalar leftVector leftDefined)
      (proportionRotation oneNonzero rightScalar rightVector rightDefined)).matrix.tt := by
  rw [← proportionRotation_mul]
  apply (proportionRotation_time_pos_iff oneNonzero _ _ _).mpr
  rw [proportionProduct_norm]
  exact OrderedExplicitField.mul_pos_direct
    ((proportionRotation_time_pos_iff oneNonzero leftScalar leftVector leftDefined).mp leftPositive)
    ((proportionRotation_time_pos_iff oneNonzero rightScalar rightVector rightDefined).mp rightPositive)

/-- Inverting a source proportion rotation with positive time entry preserves that positivity. -/
theorem proportionRotation_inverse_time_pos {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (scalar : F) (vector : Vector3 F)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0)
    (positive : 0 < (proportionRotation oneNonzero scalar vector defined).matrix.tt) :
    0 < (Basic.TernaryForm.SpecialOrthogonal.inverse
      (proportionRotation oneNonzero scalar vector defined)).matrix.tt := by
  rw [← proportionRotation_conjugate]
  apply (proportionRotation_time_pos_iff oneNonzero _ _ _).mpr
  rw [Form.quadrance_neg]
  exact (proportionRotation_time_pos_iff oneNonzero scalar vector defined).mp positive

/-- The original Lorentz identity rotation has positive time entry. -/
theorem identity_time_pos {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0) :
    0 < (Basic.TernaryForm.SpecialOrthogonal.identity (Form.lorentz oneNonzero)).matrix.tt :=
  OrderedExplicitField.zero_lt_one_direct

/-- The product of two original Lorentz rotations with positive time entry has positive time entry.

The executable projective preimages retain both input rotations. Their
source-coordinate readbacks carry the input positivity to the exact
multiplicative norm law and return the original certified product.
-/
theorem rotation_mul_time_pos {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (left right : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (leftPositive : 0 < left.matrix.tt) (rightPositive : 0 < right.matrix.tt) :
    0 < (Basic.TernaryForm.SpecialOrthogonal.mul left right).matrix.tt := by
  letI : DecidableEq F := OrderedExplicitField.eq_decidable
  let twoNonzero : (2 : F) ≠ 0 := RayOrderedExplicitField.two_ne_zero
  let leftValue := rotationProportion oneNonzero twoNonzero left
  let rightValue := rotationProportion oneNonzero twoNonzero right
  have leftReadback := proportionRotation_rotationProportion oneNonzero twoNonzero left
  have rightReadback := proportionRotation_rotationProportion oneNonzero twoNonzero right
  have positive := proportionRotation_mul_time_pos oneNonzero leftValue.scalar rightValue.scalar
    (Vector3.neg leftValue.vector) (Vector3.neg rightValue.vector)
    (rotationProportion_nonzero oneNonzero twoNonzero left)
    (rotationProportion_nonzero oneNonzero twoNonzero right)
    (by rw [leftReadback]; exact leftPositive) (by rw [rightReadback]; exact rightPositive)
  rw [leftReadback, rightReadback] at positive
  exact positive

/-- Inverting an original Lorentz rotation with positive time entry preserves that positivity. -/
theorem rotation_inverse_time_pos {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (positive : 0 < rotation.matrix.tt) :
    0 < (Basic.TernaryForm.SpecialOrthogonal.inverse rotation).matrix.tt := by
  letI : DecidableEq F := OrderedExplicitField.eq_decidable
  let twoNonzero : (2 : F) ≠ 0 := RayOrderedExplicitField.two_ne_zero
  let value := rotationProportion oneNonzero twoNonzero rotation
  have readback := proportionRotation_rotationProportion oneNonzero twoNonzero rotation
  have inversePositive := proportionRotation_inverse_time_pos oneNonzero value.scalar (Vector3.neg value.vector)
    (rotationProportion_nonzero oneNonzero twoNonzero rotation) (by rw [readback]; exact positive)
  rw [readback] at inversePositive
  exact inversePositive

end Purelib.Geometry.Rotations.Ternary.Lorentz
