module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Rotations.Basic
public import Purelib.Geometry.Rotations.Reflection
public import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Basic
open Purelib.Geometry.Rotations.Reflection
open Purelib.Geometry.Rotations.Cayley.Cap

section
@[expose] public section

/-!
# Rational rotations, section 6: half spreads

Half spread and spread are stored as executable field expressions.  For the
paper's auxiliary perpendicular direction, this module computes one of three
fixed coordinate candidates and caches both its perpendicularity and
non-nullness certificates.  No basis choice or representation theorem is
used.
-/

namespace Purelib.Geometry.Rotations.Spread

variable {K : Type*} [ExplicitField K]

/-- Definition 28: the half spread of a rotation. -/
def halfSpread (rotation : Rotation K) : K :=
  (3 - Matrix3.trace rotation.matrix) / 4

/-- The canonical executable spread of a rotation, as identified by Theorem 31. -/
def rotationSpread (rotation : Rotation K) : K :=
  4 * halfSpread rotation * (1 - halfSpread rotation)

/-- Theorem 29: the half spread of a cap is `Q/(1+Q)`. -/
theorem halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) =
      vector.quadrance / capDenominator vector := by
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  have fourCancel := ExplicitField.mul_inv_cancel 4
    (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero twoNonzero)
  unfold halfSpread capRotation
  rw [trace_cap]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 - vector.quadrance) * (capDenominator vector)⁻¹) *
        (4 : K)⁻¹ =
      (4 * vector.quadrance * (capDenominator vector)⁻¹) *
        (4 : K)⁻¹ := by
          calc
            (3 - (3 - vector.quadrance) *
                (capDenominator vector)⁻¹) * (4 : K)⁻¹ =
              (3 * (capDenominator vector *
                    (capDenominator vector)⁻¹) -
                (3 - vector.quadrance) *
                  (capDenominator vector)⁻¹) * (4 : K)⁻¹ := by
                    rw [denominatorCancel]
                    ring1
            _ = (4 * vector.quadrance *
                (capDenominator vector)⁻¹) * (4 : K)⁻¹ := by
                  unfold capDenominator
                  ring1
    _ = vector.quadrance * (capDenominator vector)⁻¹ *
        (4 * (4 : K)⁻¹) := by ring1
    _ = vector.quadrance * (capDenominator vector)⁻¹ := by
      rw [fourCancel, mul_one]

/-- Theorem 29: complementary half spread of a cap. -/
theorem one_sub_halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - halfSpread (capRotation vector defined) =
      1 / capDenominator vector := by
  have cancel := ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  rw [halfSpread_cap vector defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - vector.quadrance * (capDenominator vector)⁻¹ =
        capDenominator vector * (capDenominator vector)⁻¹ -
          vector.quadrance * (capDenominator vector)⁻¹ := by rw [cancel]
    _ = 1 * (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 29: the doubled complementary half-spread identity. -/
theorem one_sub_two_mul_halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * halfSpread (capRotation vector defined) =
      (1 - vector.quadrance) / capDenominator vector := by
  have cancel := ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  rw [halfSpread_cap vector defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - 2 * (vector.quadrance * (capDenominator vector)⁻¹) =
        capDenominator vector * (capDenominator vector)⁻¹ -
          2 * vector.quadrance * (capDenominator vector)⁻¹ := by
            rw [cancel]
            ring1
    _ = (1 - vector.quadrance) *
        (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 29: product of the two complementary half-spread factors. -/
theorem halfSpread_mul_one_sub_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) *
        (1 - halfSpread (capRotation vector defined)) =
      vector.quadrance / capDenominator vector ^ 2 := by
  rw [one_sub_halfSpread_cap vector defined twoNonzero,
    halfSpread_cap vector defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv,
    Purelib.Algebra.Field.Inverse.inverse_square defined]
  ring1

/-- Theorem 29: a cap never has half spread one. -/
theorem halfSpread_cap_ne_one (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) ≠ 1 := by
  intro spreadOne
  have complementZero :
      1 - halfSpread (capRotation vector defined) = 0 := by
    rw [spreadOne]
    ring1
  rw [one_sub_halfSpread_cap vector defined twoNonzero] at complementZero
  exact (ExplicitField.div_ne_zero
    (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero) defined) complementZero

/-- Theorem 29: recover the anchor quadrance from the half spread. -/
theorem quadrance_eq_halfSpread_div_one_sub (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    vector.quadrance =
      halfSpread (capRotation vector defined) /
        (1 - halfSpread (capRotation vector defined)) := by
  rw [one_sub_halfSpread_cap vector defined twoNonzero,
    halfSpread_cap vector defined twoNonzero]
  have denominatorInverseNonzero :=
    ExplicitField.inv_ne_zero defined
  have cancel := ExplicitField.mul_inv_cancel
    (capDenominator vector)⁻¹ denominatorInverseNonzero
  have oneDiv :
      (1 : K) / capDenominator vector =
        (capDenominator vector)⁻¹ := by
    rw [ExplicitField.div_eq_mul_inv]
    ring1
  rw [oneDiv]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    vector.quadrance = vector.quadrance * 1 := by rw [mul_one]
    _ = vector.quadrance *
        ((capDenominator vector)⁻¹ *
          ((capDenominator vector)⁻¹)⁻¹) := by rw [cancel]
    _ = vector.quadrance * (capDenominator vector)⁻¹ *
        ((capDenominator vector)⁻¹)⁻¹ := by ring1

/-- The adjugate of a rotation is its transpose, proved from explicit two-sided finite inverse certificates. -/
theorem adjugate_rotation (rotation : Rotation K) :
    Matrix3.adjugate rotation.matrix =
      Matrix3.transpose rotation.matrix := by
  have adjugateProduct :
      Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix =
        Matrix3.identity := by
    calc
      Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix =
          Matrix3.scale (Matrix3.determinant rotation.matrix)
            Matrix3.identity := Matrix3.adjugate_mul _
      _ = Matrix3.identity := by
        rw [rotation.determinantOne]
        ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1
  calc
    Matrix3.adjugate rotation.matrix =
        Matrix3.mul (Matrix3.adjugate rotation.matrix) Matrix3.identity := by
          rw [Matrix3.mul_identity]
    _ = Matrix3.mul (Matrix3.adjugate rotation.matrix)
        (Matrix3.mul rotation.matrix
          (Matrix3.transpose rotation.matrix)) := by
            rw [rotation.orthogonal]
    _ = Matrix3.mul
        (Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix)
        (Matrix3.transpose rotation.matrix) := by
          rw [Matrix3.mul_assoc]
    _ = Matrix3.transpose rotation.matrix := by
      rw [adjugateProduct, Matrix3.identity_mul]

/-- A three-dimensional rotation has equal trace and principal trace. -/
theorem principalTrace_rotation (rotation : Rotation K) :
    Matrix3.principalTrace rotation.matrix =
      Matrix3.trace rotation.matrix := by
  unfold Matrix3.principalTrace
  rw [adjugate_rotation, Matrix3.trace_transpose]

/-- The rotation trace minus one is twice one minus twice the half spread. -/
private theorem trace_sub_one_eq_halfSpread_coefficient
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace rotation.matrix - 1 =
      2 * (1 - 2 * halfSpread rotation) := by
  have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero twoNonzero
  have fourCancellation :
      4 * halfSpread rotation = 3 - Matrix3.trace rotation.matrix := by
    unfold halfSpread
    calc
      4 * ((3 - Matrix3.trace rotation.matrix) / 4) =
          ((3 - Matrix3.trace rotation.matrix) / 4) * 4 := by ring1
      _ = 3 - Matrix3.trace rotation.matrix :=
        ExplicitField.div_mul_cancel _ fourNonzero
  calc
    Matrix3.trace rotation.matrix - 1 =
        2 * (1 - 2 * halfSpread rotation) +
          (4 * halfSpread rotation -
            (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = 2 * (1 - 2 * halfSpread rotation) := by
      rw [fourCancellation]
      ring1

/-- Theorem 29: characteristic polynomial of an arbitrary rotation in terms of its half spread. -/
theorem characteristicValue_rotation (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) *
        (X ^ 2 - 2 * (1 - 2 * halfSpread rotation) * X + 1) := by
  calc
    Matrix3.characteristicValue rotation.matrix X =
        X ^ 3 - Matrix3.trace rotation.matrix * X ^ 2 +
          Matrix3.principalTrace rotation.matrix * X -
            Matrix3.determinant rotation.matrix :=
      Matrix3.characteristicValue_expansion _ _
    _ = X ^ 3 - Matrix3.trace rotation.matrix * X ^ 2 +
          Matrix3.trace rotation.matrix * X - 1 := by
      rw [principalTrace_rotation, rotation.determinantOne]
    _ = (X - 1) *
        (X ^ 2 - (Matrix3.trace rotation.matrix - 1) * X + 1) := by
      ring1
    _ = (X - 1) *
        (X ^ 2 - 2 * (1 - 2 * halfSpread rotation) * X + 1) := by
      rw [trace_sub_one_eq_halfSpread_coefficient rotation twoNonzero]

/-- A rotation has the unipotent characteristic polynomial `(X - 1)^3` exactly when its half spread is zero. The
converse uses only the two displayed evaluations at `1` and `-1`, so it neither compares polynomial coefficients nor
appeals to an infinite-root argument. -/
theorem characteristicUnipotent_iff_halfSpread_eq_zero
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) ↔
      halfSpread rotation = 0 := by
  constructor
  · intro characteristic
    have atOne := characteristic 1
    rw [Matrix3.characteristicValue_expansion,
      rotation.determinantOne] at atOne
    have principalEqTrace :
        Matrix3.principalTrace rotation.matrix =
          Matrix3.trace rotation.matrix := by
      calc
        Matrix3.principalTrace rotation.matrix =
            (1 ^ 3 - Matrix3.trace rotation.matrix * 1 ^ 2 +
                Matrix3.principalTrace rotation.matrix * 1 - 1) +
              Matrix3.trace rotation.matrix := by ring1
        _ = (1 - 1) ^ 3 + Matrix3.trace rotation.matrix := by
          rw [atOne]
        _ = Matrix3.trace rotation.matrix := by ring1
    have atNegativeOne := characteristic (-1)
    rw [Matrix3.characteristicValue_expansion,
      rotation.determinantOne] at atNegativeOne
    have tracePlusPrincipal :
        Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix = 6 := by
      calc
        Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix =
          -((-1) ^ 3 - Matrix3.trace rotation.matrix * (-1) ^ 2 +
              Matrix3.principalTrace rotation.matrix * (-1) - 1) - 2 := by
            ring1
        _ = -((-1 - 1) ^ 3) - 2 := by rw [atNegativeOne]
        _ = 6 := by ring1
    have twiceTrace : 2 * Matrix3.trace rotation.matrix = 6 := by
      calc
        2 * Matrix3.trace rotation.matrix =
            Matrix3.trace rotation.matrix +
              Matrix3.principalTrace rotation.matrix := by
          rw [principalEqTrace]
          ring1
        _ = 6 := tracePlusPrincipal
    have traceDifferenceZero :
        Matrix3.trace rotation.matrix - 3 = 0 := by
      apply ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
      calc
        2 * (Matrix3.trace rotation.matrix - 3) =
            2 * Matrix3.trace rotation.matrix - 6 := by ring1
        _ = 0 := by rw [twiceTrace]; ring1
    have traceEqThree : Matrix3.trace rotation.matrix = 3 := by
      calc
        Matrix3.trace rotation.matrix =
            (Matrix3.trace rotation.matrix - 3) + 3 := by ring1
        _ = 0 + 3 := by rw [traceDifferenceZero]
        _ = 3 := by ring1
    unfold halfSpread
    rw [traceEqThree]
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  · intro spreadZero X
    rw [characteristicValue_rotation rotation twoNonzero X, spreadZero]
    ring1

/-- A reflection has trace one. -/
theorem trace_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.trace (reflection vector nonNull) = 1 := by
  have cancel := ExplicitField.mul_inv_cancel
    vector.quadrance nonNull
  unfold Matrix3.trace reflection Matrix3.sub Matrix3.identity Matrix3.scale
    Matrix3.outer Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    _ = 3 - 2 * (vector.quadrance * vector.quadrance⁻¹) := by
      unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
      ring1
    _ = 1 := by rw [cancel]; ring1

/-- A half turn has trace minus one. -/
theorem trace_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.trace (halfTurn vector nonNull) = -1 := by
  unfold halfTurn
  rw [show Matrix3.trace (Matrix3.neg (reflection vector nonNull)) =
      -Matrix3.trace (reflection vector nonNull) by
        unfold Matrix3.trace Matrix3.neg
        ring1,
    trace_reflection]

/-- Theorem 29: every half turn has half spread one. -/
theorem halfSpread_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (halfTurnRotation vector nonNull) = 1 := by
  have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero twoNonzero
  have fourCancel := ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have numerator : (3 - (-1 : K)) = 4 := by ring1
  unfold halfSpread halfTurnRotation
  rw [trace_halfTurn]
  rw [numerator, ExplicitField.div_eq_mul_inv]
  exact fourCancel

/-- Orthogonal action by a bundled rotation preserves quadrance. -/
theorem quadrance_rowMul_rotation (rotation : Rotation K)
    (vector : Vector K) :
    Coordinates3.Vector.quadrance (Matrix3.rowMul vector rotation.matrix) =
      Coordinates3.Vector.quadrance vector :=
  Matrix3.quadrance_rowMul_of_isOrthogonal rotation.orthogonal vector

/-- A non-null vector remains non-null after rotation. -/
theorem rowMul_rotation_nonNull (rotation : Rotation K)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    (Matrix3.rowMul vector rotation.matrix).quadrance ≠ 0 := by
  rw [quadrance_rowMul_rotation]
  exact nonNull

/-- Definition 30 evaluated at one supplied non-null direction. -/
def rotationSpreadAt (rotation : Rotation K) (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) : K :=
  Coordinates3.Vector.spread vector (Matrix3.rowMul vector rotation.matrix)
    nonNull (rowMul_rotation_nonNull rotation vector nonNull)

/-- Quadratic reduction of a cap on a direction perpendicular to its anchor axis. -/
theorem rowMul_cap_of_perpendicular (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (vector : Vector K)
    (perpendicular : vector.Perpendicular axis) :
    Matrix3.rowMul vector (cap axis defined) =
      Coordinates3.Vector.add
        (Coordinates3.Vector.scale
          ((1 - axis.quadrance) / capDenominator axis) vector)
        (Coordinates3.Vector.scale (2 / capDenominator axis)
          (Coordinates3.Vector.cross axis vector)) := by
  have reversePerpendicular : Coordinates3.Vector.dot axis vector = 0 := by
    unfold Coordinates3.Vector.Perpendicular at perpendicular
    rw [Coordinates3.Vector.dot_comm]
    exact perpendicular
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (capDenominator axis) defined
  have coefficient :
      1 - (2 / capDenominator axis) * axis.quadrance =
        (1 - axis.quadrance) / capDenominator axis := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 - 2 * (capDenominator axis)⁻¹ * axis.quadrance =
          capDenominator axis * (capDenominator axis)⁻¹ -
            2 * axis.quadrance * (capDenominator axis)⁻¹ := by
              rw [denominatorCancel]
              ring1
      _ = (1 - axis.quadrance) * (capDenominator axis)⁻¹ := by
        unfold capDenominator
        ring1
  calc
    Matrix3.rowMul vector (cap axis defined) =
        Coordinates3.Vector.add vector
          (Coordinates3.Vector.scale (2 / capDenominator axis)
            (Coordinates3.Vector.add (Coordinates3.Vector.cross axis vector)
              (Coordinates3.Vector.sub
                (Coordinates3.Vector.scale (Coordinates3.Vector.dot axis vector) axis)
                (Coordinates3.Vector.scale axis.quadrance vector)))) := by
      unfold cap
      rw [Matrix3.rowMul_add, Matrix3.rowMul_identity,
        Matrix3.rowMul_scale, Matrix3.rowMul_add, Antisymmetric.rowMul_anchor,
        ← Matrix3.rowMul_mul, Antisymmetric.rowMul_anchor, Antisymmetric.rowMul_anchor,
        Coordinates3.Vector.vector_triple_product]
      rfl
    _ = Coordinates3.Vector.add
        (Coordinates3.Vector.scale
          (1 - (2 / capDenominator axis) * axis.quadrance) vector)
        (Coordinates3.Vector.scale (2 / capDenominator axis)
          (Coordinates3.Vector.cross axis vector)) := by
      rw [reversePerpendicular]
      ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.sub Coordinates3.Vector.scale <;> ring1
    _ = Coordinates3.Vector.add
        (Coordinates3.Vector.scale
          ((1 - axis.quadrance) / capDenominator axis) vector)
        (Coordinates3.Vector.scale (2 / capDenominator axis)
          (Coordinates3.Vector.cross axis vector)) := by rw [coefficient]

/-- Dot-product component of the perpendicular cap action. -/
theorem dot_self_rowMul_cap_of_perpendicular (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (vector : Vector K)
    (perpendicular : vector.Perpendicular axis) :
    Coordinates3.Vector.dot vector (Matrix3.rowMul vector (cap axis defined)) =
      ((1 - axis.quadrance) / capDenominator axis) *
        vector.quadrance := by
  have crossPerpendicular :
      Coordinates3.Vector.dot vector (Coordinates3.Vector.cross axis vector) = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact Coordinates3.Vector.cross_dot_right axis vector
  rw [rowMul_cap_of_perpendicular axis defined vector perpendicular,
    Coordinates3.Vector.dot_add_right, Coordinates3.Vector.dot_scale_right,
    Coordinates3.Vector.dot_scale_right, crossPerpendicular]
  unfold Coordinates3.Vector.quadrance
  ring1

/-- Theorem 31 for a cap: every admissible perpendicular direction computes the same canonical rotation spread. -/
theorem rotationSpreadAt_cap (axis : Vector K)
    (defined : capDenominator axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0)
    (perpendicular : vector.Perpendicular axis) :
    rotationSpreadAt (capRotation axis defined) vector nonNull =
      rotationSpread (capRotation axis defined) := by
  have vectorSquareNonzero : vector.quadrance * vector.quadrance ≠ 0 :=
    ExplicitField.mul_ne_zero nonNull nonNull
  have vectorSquareCancel := ExplicitField.mul_inv_cancel
    (vector.quadrance * vector.quadrance) vectorSquareNonzero
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (capDenominator axis) defined
  have capQuadrance :
      (Matrix3.rowMul vector (cap axis defined)).quadrance =
        vector.quadrance :=
    Matrix3.quadrance_rowMul_of_isOrthogonal
      (cap_isOrthogonal axis defined) vector
  unfold rotationSpreadAt Coordinates3.Vector.spread rotationSpread
  change
    1 - Coordinates3.Vector.dot vector (Matrix3.rowMul vector (cap axis defined)) ^ 2 /
        (vector.quadrance *
          (Matrix3.rowMul vector (cap axis defined)).quadrance) =
      4 * halfSpread (capRotation axis defined) *
        (1 - halfSpread (capRotation axis defined))
  rw [dot_self_rowMul_cap_of_perpendicular axis defined vector perpendicular,
    capQuadrance,
    one_sub_halfSpread_cap axis defined twoNonzero,
    halfSpread_cap axis defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 -
        (((1 - axis.quadrance) * (capDenominator axis)⁻¹) *
          vector.quadrance) ^ 2 *
          (vector.quadrance * vector.quadrance)⁻¹ =
      1 - ((1 - axis.quadrance) *
        (capDenominator axis)⁻¹) ^ 2 := by
          calc
            1 -
                (((1 - axis.quadrance) *
                    (capDenominator axis)⁻¹) *
                  vector.quadrance) ^ 2 *
                  (vector.quadrance * vector.quadrance)⁻¹ =
              1 - ((1 - axis.quadrance) *
                  (capDenominator axis)⁻¹) ^ 2 *
                ((vector.quadrance * vector.quadrance) *
                  (vector.quadrance * vector.quadrance)⁻¹) := by ring1
            _ = 1 - ((1 - axis.quadrance) *
                (capDenominator axis)⁻¹) ^ 2 := by
              rw [vectorSquareCancel]
              ring1
    _ = 4 * (axis.quadrance * (capDenominator axis)⁻¹) *
        (1 * (capDenominator axis)⁻¹) := by
      calc
        1 - ((1 - axis.quadrance) *
            (capDenominator axis)⁻¹) ^ 2 =
          (capDenominator axis * (capDenominator axis)⁻¹) ^ 2 -
            ((1 - axis.quadrance) *
              (capDenominator axis)⁻¹) ^ 2 := by
                rw [denominatorCancel]
                ring1
        _ = 4 * (axis.quadrance * (capDenominator axis)⁻¹) *
            (1 * (capDenominator axis)⁻¹) := by
          unfold capDenominator
          ring1

/-- A half turn has its canonical rotation spread in every perpendicular non-null direction.

The axis and tested vector must be non-null, and two must be nonzero; under these conditions the directional spread
equals the half turn's rotation spread (Theorem 31). -/
theorem rotationSpreadAt_halfTurn (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0)
    (perpendicular : vector.Perpendicular axis) :
    rotationSpreadAt (halfTurnRotation axis axisNonNull) vector nonNull =
      rotationSpread (halfTurnRotation axis axisNonNull) := by
  have squareNonzero : vector.quadrance * vector.quadrance ≠ 0 :=
    ExplicitField.mul_ne_zero nonNull nonNull
  have squareCancel := ExplicitField.mul_inv_cancel
    (vector.quadrance * vector.quadrance) squareNonzero
  unfold rotationSpreadAt Coordinates3.Vector.spread rotationSpread
  rw [show Matrix3.rowMul vector
      (halfTurnRotation axis axisNonNull).matrix = Coordinates3.Vector.neg vector by
        exact rowMul_halfTurn_of_perpendicular axis axisNonNull twoNonzero
          vector perpendicular,
    Coordinates3.Vector.dot_neg_right, Coordinates3.Vector.quadrance_neg,
    halfSpread_halfTurn axis axisNonNull twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - (-Coordinates3.Vector.dot vector vector) ^ 2 *
        (vector.quadrance * vector.quadrance)⁻¹ =
      1 - (vector.quadrance * vector.quadrance) *
        (vector.quadrance * vector.quadrance)⁻¹ := by
          unfold Coordinates3.Vector.quadrance
          ring1
    _ = 0 := by rw [squareCancel]; ring1
    _ = 4 * 1 * (1 - 1) := by ring1

/-- Independence of the perpendicular direction in Definition 30 for caps. -/
theorem rotationSpreadAt_cap_independent (axis : Vector K)
    (defined : capDenominator axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular : first.Perpendicular axis)
    (secondPerpendicular : second.Perpendicular axis) :
    rotationSpreadAt (capRotation axis defined) first firstNonNull =
      rotationSpreadAt (capRotation axis defined) second secondNonNull := by
  rw [rotationSpreadAt_cap axis defined twoNonzero first firstNonNull
      firstPerpendicular,
    rotationSpreadAt_cap axis defined twoNonzero second secondNonNull
      secondPerpendicular]

/-- Independence of the perpendicular direction in Definition 30 for half turns. -/
theorem rotationSpreadAt_halfTurn_independent (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular : first.Perpendicular axis)
    (secondPerpendicular : second.Perpendicular axis) :
    rotationSpreadAt (halfTurnRotation axis axisNonNull) first firstNonNull =
    rotationSpreadAt (halfTurnRotation axis axisNonNull) second secondNonNull := by
  rw [rotationSpreadAt_halfTurn axis axisNonNull twoNonzero first firstNonNull
      firstPerpendicular,
    rotationSpreadAt_halfTurn axis axisNonNull twoNonzero second secondNonNull
      secondPerpendicular]

/-- Trace calculation underlying Theorem 32. -/
theorem trace_reflection_product (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.trace
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      3 - 4 * Coordinates3.Vector.spread first second firstNonNull secondNonNull := by
  have firstCancel := ExplicitField.mul_inv_cancel
    first.quadrance firstNonNull
  have secondCancel := ExplicitField.mul_inv_cancel
    second.quadrance secondNonNull
  have productInverse :
      (first.quadrance * second.quadrance)⁻¹ =
        first.quadrance⁻¹ * second.quadrance⁻¹ :=
    Purelib.Algebra.Field.Inverse.inverse_product firstNonNull secondNonNull
  calc
    Matrix3.trace
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      -1 + 4 * Coordinates3.Vector.dot first second ^ 2 *
        first.quadrance⁻¹ * second.quadrance⁻¹ := by
          unfold Matrix3.trace Matrix3.mul reflection Matrix3.sub
            Matrix3.identity Matrix3.scale Matrix3.outer
          simp only [ExplicitField.div_eq_mul_inv]
          calc
            _ = 3 - 2 * (first.quadrance * first.quadrance⁻¹) -
                2 * (second.quadrance * second.quadrance⁻¹) +
                4 * Coordinates3.Vector.dot first second ^ 2 *
                  first.quadrance⁻¹ * second.quadrance⁻¹ := by
                    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
                    ring1
            _ = -1 + 4 * Coordinates3.Vector.dot first second ^ 2 *
                first.quadrance⁻¹ * second.quadrance⁻¹ := by
              rw [firstCancel, secondCancel]
              ring1
    _ = 3 - 4 * Coordinates3.Vector.spread first second firstNonNull secondNonNull := by
      unfold Coordinates3.Vector.spread
      simp only [ExplicitField.div_eq_mul_inv, productInverse]
      ring1

/-- Theorem 32: the half spread of a product of two reflections is the spread between their non-null normals. -/
theorem halfSpread_reflectionProduct (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (reflectionProductRotation first second firstNonNull secondNonNull) =
      Coordinates3.Vector.spread first second firstNonNull secondNonNull := by
  have fourCancel := ExplicitField.mul_inv_cancel (4 : K)
    (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero twoNonzero)
  unfold halfSpread reflectionProductRotation
  rw [trace_reflection_product]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 - 4 * Coordinates3.Vector.spread first second firstNonNull secondNonNull)) *
        (4 : K)⁻¹ =
      Coordinates3.Vector.spread first second firstNonNull secondNonNull *
        (4 * (4 : K)⁻¹) := by ring1
    _ = Coordinates3.Vector.spread first second firstNonNull secondNonNull := by
      rw [fourCancel, mul_one]

end Purelib.Geometry.Rotations.Spread

end

end

section
@[expose] public section

/-!
# Section 13.3: open problems

Problem 68 is refuted as printed by the projection counterexample already
recorded for Conjecture 52; its hardened unital five-parameter replacement is
proved over the paper's primary rational field.  For Problem 69, the missing PDF glyph is the
quadrance-class homomorphism `chi`, represented here by
`RotationQuadranceClass.ofRotation`; the exact excluded affine quadric is
`Q = -1`.  The executable finite enumerators and small-field regression
tables live in `FiniteFieldCounting`.  Problems 70 and 71 retain the pointwise
finite data and algebraic parts that follow from the preceding development;
Problem 70's finitely generated subgroup clause is classified through exact
arbitrary finite-word queries and its complete finite `chi` quotient;
Problem 72 is completed by the constructive projective polarity in
`ProjectiveDuality`.
-/

namespace Purelib.Geometry.Rotations.Spread

variable {K : Type*} [ExplicitField K]

/-! ## Problem 69 -/

/-- Pointwise membership in a half-spread fiber. This is the finite equation whose global fiber sizes Problem 69 asks to
determine. -/
def InHalfSpreadFiber (rotation : Rotation K) (value : K) : Prop :=
  halfSpread rotation = value
end Purelib.Geometry.Rotations.Spread

end
