module

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.ExplicitOrder.Basic
public import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Geometry.Quadratic.Space3.Ordered
public import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.LinearAlgebra.Coordinates3.Ray
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Algebra.Field.ExplicitOrder.Basic
open Purelib.Algebra.Field.ExplicitOrder.Sign

open Purelib.Geometry

open Purelib.Geometry.Quadratic.Space3.Ordered

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Axis

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Rational rotations, section 8: handedness

Handedness is stored as the determinant of the displayed frame formed by an
anchor axis, a perpendicular vector, and its rotated image.  The determinant
formula is valid over every explicit field.  Positivity is separated into a
small coherent ordered-field interface so the algebraic theorem remains
available over finite fields.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Rotations.Orientation.Handedness

/-- The inverse rotation, represented by the certified transpose matrix. -/
def inverseRotation (rotation : Rotations.Basic.Rotation K) :
  Rotations.Basic.Rotation K where
  matrix := Matrix3.transpose rotation.matrix
  orthogonal := by
    unfold Purelib.LinearAlgebra.Coordinates3.Matrix3.IsOrthogonal
    rw [Matrix3.transpose_transpose]
    exact Recovery.transpose_mul_rotation rotation
  determinantOne := by
    rw [Matrix3.determinant_transpose, rotation.determinantOne]

/-- Inverting a certified rotation preserves its half spread. -/
theorem halfSpread_inverseRotation (rotation :
  Rotations.Basic.Rotation K) :
    Spread.halfSpread (Orientation.Handedness.inverseRotation rotation) = Spread.halfSpread rotation := by
  unfold Spread.halfSpread Orientation.Handedness.inverseRotation
  rw [Matrix3.trace_transpose]

/-- The inverse of a rotation whose half spread differs from one also has half spread different from one. -/
theorem inverseRotation_notHalfTurn (rotation :
  Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    Spread.halfSpread (inverseRotation rotation) ≠ 1 := by
  rw [halfSpread_inverseRotation]
  exact notHalfTurn

/-- The introductory identity of Section 8: inversion negates the recovered anchor matrix. -/
theorem rotationAnchor_inverseRotation (rotation :
  Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    Recovery.rotationAnchor (Orientation.Handedness.inverseRotation rotation)
        (inverseRotation_notHalfTurn rotation notHalfTurn) =
      Matrix3.neg (Recovery.rotationAnchor rotation notHalfTurn) := by
  unfold Recovery.rotationAnchor Orientation.Handedness.inverseRotation
  rw [Matrix3.trace_transpose, Matrix3.transpose_transpose]
  ext <;> unfold Matrix3.scale Matrix3.sub Matrix3.neg <;> ring1

/-- In vector coordinates, inversion reverses the anchor direction. -/
theorem rotationAnchorVector_inverseRotation (rotation :
  Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Recovery.rotationAnchorVector (inverseRotation rotation)
        (inverseRotation_notHalfTurn rotation notHalfTurn) =
      Coordinates3.Vector.neg (Recovery.rotationAnchorVector rotation notHalfTurn) := by
  apply Antisymmetric.anchor_injective
  rw [Recovery.anchor_rotationAnchorVector _ _ twoNonzero, Antisymmetric.anchor_neg,
    Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero,
    rotationAnchor_inverseRotation]

/-- The determinant of the axis/transversal/rotated-transversal frame. -/
def handednessDet (axis transversal : Coordinates3.Vector K)
  (matrix : Coordinates3.Matrix3 K) : K :=
  Coordinates3.Vector.determinant axis transversal (Matrix3.rowMul transversal matrix)

/-- Compute a cap's handedness determinant from axis and transversal quadrances.

For a transversal perpendicular to the axis, the determinant is `2 Q(axis) Q(transversal) / (1 + Q(axis))`; the axis
must have a defined cap (Theorem 41). -/
theorem handednessDet_cap (axis : Coordinates3.Vector K)
    (defined : Cap.capDenominator axis ≠ 0) (transversal : Coordinates3.Vector K)
    (perpendicular : transversal.Perpendicular axis) :
    Orientation.Handedness.handednessDet axis transversal (Cap.cap axis defined) =
      (2 * axis.quadrance / Cap.capDenominator axis) *
        transversal.quadrance := by
  have reversePerpendicular : Coordinates3.Vector.dot axis transversal = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact perpendicular
  have lagrange := Coordinates3.Vector.lagrange axis transversal
  rw [reversePerpendicular] at lagrange
  have crossQuadrance :
      (Coordinates3.Vector.cross axis transversal).quadrance =
        axis.quadrance * transversal.quadrance := by
    calc
      (Coordinates3.Vector.cross axis transversal).quadrance =
          0 ^ 2 + (Coordinates3.Vector.cross axis transversal).quadrance := by ring1
      _ = axis.quadrance * transversal.quadrance := lagrange
  unfold Orientation.Handedness.handednessDet
  rw [Spread.rowMul_cap_of_perpendicular axis defined transversal perpendicular,
    Coordinates3.Vector.determinant_add_third, Coordinates3.Vector.determinant_scale_third,
    Coordinates3.Vector.determinant_repeat_second, mul_zero, zero_add,
    Coordinates3.Vector.determinant_scale_third,
    ← Coordinates3.Vector.scalar_triple_product]
  change (2 / Cap.capDenominator axis) *
      (Coordinates3.Vector.cross axis transversal).quadrance =
    (2 * axis.quadrance / Cap.capDenominator axis) *
      transversal.quadrance
  rw [crossQuadrance]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- Express a cap's handedness determinant using its half spread.

For a perpendicular transversal and nonzero two, the determinant is twice the half spread times its complement, the cap
denominator and the transversal quadrance (Theorem 41). -/
theorem handednessDet_cap_halfSpread (axis :
  Coordinates3.Vector K)
    (defined : Cap.capDenominator axis ≠ 0) (transversal : Coordinates3.Vector K)
    (perpendicular : transversal.Perpendicular axis)
    (twoNonzero : (2 : K) ≠ 0) :
    handednessDet axis transversal (Cap.cap axis defined) =
      2 * Spread.halfSpread (Cap.capRotation axis defined) *
        (1 - Spread.halfSpread (Cap.capRotation axis defined)) *
        Cap.capDenominator axis * transversal.quadrance := by
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (Cap.capDenominator axis) defined
  rw [handednessDet_cap axis defined transversal perpendicular,
    Spread.one_sub_halfSpread_cap axis defined twoNonzero,
    Spread.halfSpread_cap axis defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    2 * axis.quadrance * (Cap.capDenominator axis)⁻¹ *
        transversal.quadrance =
      2 * axis.quadrance * (Cap.capDenominator axis)⁻¹ *
        (Cap.capDenominator axis * (Cap.capDenominator axis)⁻¹) *
        transversal.quadrance := by rw [denominatorCancel]; ring1
    _ = 2 * (axis.quadrance * (Cap.capDenominator axis)⁻¹) *
        (1 * (Cap.capDenominator axis)⁻¹) *
        Cap.capDenominator axis * transversal.quadrance := by ring1

/-- The metric handedness determinant vanishes identically on a null anchor axis.

The supplied perpendicular transversal and nonzero cap denominator retain the original cap construction, while the
anchor quadrance makes its metric determinant zero. -/
theorem handednessDet_cap_of_null (axis : Coordinates3.Vector
  K)
    (defined : Cap.capDenominator axis ≠ 0) (transversal : Coordinates3.Vector K)
    (perpendicular : transversal.Perpendicular axis)
    (null : axis.quadrance = 0) :
    handednessDet axis transversal (Cap.cap axis defined) = 0 := by
  rw [handednessDet_cap axis defined transversal perpendicular, null]
  simp only [mul_zero, ExplicitField.zero_div, zero_mul, -eq_self, -iff_self]
  rfl

/-- Reversing the anchor while retaining the same displayed first frame row reverses the handedness determinant. -/
theorem handednessDet_cap_neg_sameAxis (axis :
  Coordinates3.Vector K)
    (defined : Cap.capDenominator axis ≠ 0) (transversal : Coordinates3.Vector K)
    (perpendicular : transversal.Perpendicular axis) :
    Orientation.Handedness.handednessDet axis transversal
        (Cap.cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined)) =
      -((2 * axis.quadrance / Cap.capDenominator axis) *
        transversal.quadrance) := by
  have negPerpendicular : transversal.Perpendicular (Coordinates3.Vector.neg axis) := by
    unfold Coordinates3.Vector.Perpendicular at *
    rw [Coordinates3.Vector.dot_neg_right, perpendicular]
    ring1
  have formula := handednessDet_cap (Coordinates3.Vector.neg axis)
    (Cap.cap_neg_defined axis defined) transversal negPerpendicular
  unfold Orientation.Handedness.handednessDet at formula ⊢
  rw [Coordinates3.Vector.determinant_neg_first, Coordinates3.Vector.quadrance_neg,
    Cap.capDenominator_neg] at formula
  calc
    Coordinates3.Vector.determinant axis transversal
        (Matrix3.rowMul transversal
          (Cap.cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined))) =
      -(-Coordinates3.Vector.determinant axis transversal
        (Matrix3.rowMul transversal
          (Cap.cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined)))) := by ring1
    _ = -((2 * axis.quadrance / Cap.capDenominator axis) *
        transversal.quadrance) := by rw [formula]

end Purelib.Geometry.Rotations.Orientation.Handedness

section Ordered

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

namespace Purelib.Geometry.Rotations.Orientation.Handedness

/-- Use the displayed ordered field's executable equality decision. -/
local instance instDecidableEq_purelib_1 : DecidableEq F :=
  OrderedExplicitField.eq_decidable

/-- Corollary 42: the anchor/transversal/rotated-transversal frame is strictly positively oriented over an ordered
field. -/
theorem rightHandRule (axis transversal : Coordinates3.Vector
  F)
    (defined : Cap.capDenominator axis ≠ 0)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero)
    (transversalNonzero : transversal ≠ Coordinates3.Vector.zero)
    (perpendicular : transversal.Perpendicular axis) :
    0 < handednessDet axis transversal (Cap.cap axis defined) := by
  rw [handednessDet_cap axis defined transversal perpendicular]
  have axisPositive := Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims.vectorQuadrancePositive axis
    axisNonzero
  have transversalPositive :=
    Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims.vectorQuadrancePositive transversal transversalNonzero
  have denominatorPositive : 0 < Cap.capDenominator axis := by
    unfold Cap.capDenominator
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct axisPositive
  have twoPositive : 0 < (2 : F) := by
    rw [show (2 : F) = 1 + 1 by ring1]
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct
      OrderedExplicitField.zero_lt_one_direct
  have coefficientPositive :
      0 < 2 * axis.quadrance / Cap.capDenominator axis := by
    rw [ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct
      (OrderedExplicitField.mul_pos_direct twoPositive axisPositive)
      (OrderedExplicitField.inv_pos_direct denominatorPositive)
  exact OrderedExplicitField.mul_pos_direct coefficientPositive
    transversalPositive

end Purelib.Geometry.Rotations.Orientation.Handedness

end Ordered

namespace Purelib.Geometry.Rotations.Orientation.Handedness

/-- Negating an anchor preserves the half spread of its cap. -/
theorem halfSpread_cap_neg (axis : Coordinates3.Vector K)
    (defined : Cap.capDenominator axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread
        (Cap.capRotation (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined)) =
      Spread.halfSpread (Cap.capRotation axis defined) := by
  rw [Spread.halfSpread_cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined)
      twoNonzero,
    Spread.halfSpread_cap axis defined twoNonzero,
    Coordinates3.Vector.quadrance_neg, Cap.capDenominator_neg]

/-- Corollary 42's algebraic distinction: opposite nonzero anchors give different inverse rotations, even when no order
is available. -/
theorem cap_ne_cap_neg_of_ne_zero (axis : Coordinates3.Vector
  K)
    (defined : Cap.capDenominator axis ≠ 0) (axisNonzero : axis ≠ Coordinates3.Vector.zero)
    (twoNonzero : (2 : K) ≠ 0) :
    Cap.cap axis defined ≠
      Cap.cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined) := by
  intro equalCaps
  have selfNegative := Cap.cap_injective twoNonzero axis (Coordinates3.Vector.neg axis)
    defined (Cap.cap_neg_defined axis defined) equalCaps
  exact axisNonzero
    (Purelib.LinearAlgebra.Coordinates3.Vector.eq_zero_of_eq_neg axis twoNonzero selfNegative)

end Purelib.Geometry.Rotations.Orientation.Handedness

end

end

public section

section

namespace Purelib.Geometry.Rotations.Orientation.Handedness

/-- Inversion takes a nonzero recovered Euclidean anchor to its distinct opposite ray.

The original rotation and its certified inverse have exactly opposite
recovered vectors. Positive rescaling cannot identify these two nonzero
vectors, independently of any choice of perpendicular test vector.
-/
theorem rotationAnchorVector_inverse_distinct_ray {F : Type*} [RayOrderedExplicitField F]
    (rotation : Basic.Rotation F) (notHalfTurn : Spread.halfSpread rotation ≠ 1) (twoNonzero : (2 : F) ≠ 0)
    (anchorNonzero : Recovery.rotationAnchorVector rotation notHalfTurn ≠ Coordinates3.Vector.zero) :
    ¬ Coordinates3.Vector.RayEquivalent (Recovery.rotationAnchorVector rotation notHalfTurn)
      (Recovery.rotationAnchorVector (inverseRotation rotation)
        (inverseRotation_notHalfTurn rotation notHalfTurn)) := by
  rw [rotationAnchorVector_inverseRotation rotation notHalfTurn twoNonzero]
  exact Coordinates3.Vector.not_rayEquivalent_neg _ anchorNonzero

/-- Inverting a nonzero cap reverses its strict orientation about the original axis.

The first frame vector remains the original axis. Nonzero perpendicular axis
and transversal vectors give a positive original determinant; the retained
difference law turns its negative into a strict comparison with zero.
-/
theorem inverseRightHandRule {F : Type*} [RayOrderedExplicitField F]
    (law : OrderDifferenceLaw F) (axis transversal : Coordinates3.Vector F)
    (defined : Cap.capDenominator axis ≠ 0)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero)
    (transversalNonzero : transversal ≠ Coordinates3.Vector.zero)
    (perpendicular : transversal.Perpendicular axis) :
    handednessDet axis transversal
      (Cap.cap (Coordinates3.Vector.neg axis) (Cap.cap_neg_defined axis defined)) < 0 := by
  have positive := rightHandRule axis transversal defined axisNonzero transversalNonzero perpendicular
  have original := handednessDet_cap axis defined transversal perpendicular
  have reversed := handednessDet_cap_neg_sameAxis axis defined transversal perpendicular
  apply (law.lt_zero_iff _).mpr
  rw [reversed]
  have doubleNegative :
      -(-((2 * axis.quadrance / Cap.capDenominator axis) * transversal.quadrance)) =
        (2 * axis.quadrance / Cap.capDenominator axis) * transversal.quadrance := by ring1
  rw [doubleNegative]
  exact original ▸ positive

end Purelib.Geometry.Rotations.Orientation.Handedness

end
