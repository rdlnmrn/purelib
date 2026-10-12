module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector

import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
public import Purelib.Geometry.Rotations.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.LinearAlgebra

@[expose] public section

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Basic
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
namespace Purelib.Geometry.Rotations.Reflection
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The non-null reflection coefficient satisfies the scalar identity giving involutivity. -/
private theorem reflection_coefficient (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    (2 / vector.quadrance) ^ 2 * vector.quadrance =
      2 * (2 / vector.quadrance) := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (2 * vector.quadrance⁻¹) ^ 2 * vector.quadrance =
        4 * (vector.quadrance * vector.quadrance⁻¹) *
          vector.quadrance⁻¹ := by ring1
    _ = 2 * (2 * vector.quadrance⁻¹) := by rw [cancel]; ring1

end Purelib.Geometry.Rotations.Reflection
end

namespace Purelib.Geometry.Rotations.Reflection

open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Definition 14: reflection in the plane perpendicular to a non-null vector. -/
def reflection (vector : Vector K) (_nonNull : vector.quadrance ≠ 0) :
    Matrix3 K :=
  Matrix3.sub Matrix3.identity
    (Matrix3.scale (2 / vector.quadrance) (Matrix3.outer vector vector))

/-- The row-vector action of a reflection, in the formula used throughout the paper. -/
theorem rowMul_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (other : Vector K) :
    Matrix3.rowMul other (reflection vector nonNull) =
      Coordinates3.Vector.sub other
        (Coordinates3.Vector.scale (2 * Coordinates3.Vector.dot other vector / vector.quadrance) vector) := by
  ext <;> unfold Matrix3.rowMul reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Coordinates3.Vector.sub Coordinates3.Vector.scale Coordinates3.Vector.dot
    Coordinates3.Vector.quadrance <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1

/-- The reflection is symmetric. -/
theorem reflection_transpose (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.transpose (reflection vector nonNull) = reflection vector nonNull := by
  unfold reflection
  rw [Matrix3.transpose_sub, Matrix3.transpose_identity,
    Matrix3.transpose_scale, Matrix3.outer_transpose]

/-- Theorem 15.1: reflection is an involution. -/
theorem reflection_square (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.mul (reflection vector nonNull) (reflection vector nonNull) =
      Matrix3.identity := by
  have coefficientZero :
      (2 / vector.quadrance) ^ 2 * vector.quadrance -
        2 * (2 / vector.quadrance) = 0 := by
    rw [Purelib.Geometry.Rotations.Reflection.reflection_coefficient vector nonNull]
    ring1
  calc
    Matrix3.mul (reflection vector nonNull) (reflection vector nonNull) =
        Matrix3.add Matrix3.identity
          (Matrix3.scale
            ((2 / vector.quadrance) ^ 2 * vector.quadrance -
              2 * (2 / vector.quadrance))
            (Matrix3.outer vector vector)) := by
      ext <;> unfold reflection Matrix3.mul Matrix3.sub Matrix3.add
        Matrix3.identity Matrix3.scale Matrix3.outer Coordinates3.Vector.quadrance
        Coordinates3.Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.outer
        Matrix3.identity <;> ring1

/-- Theorem 15.2: the normal vector is negated by its reflection. -/
theorem rowMul_self_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.rowMul vector (reflection vector nonNull) = Coordinates3.Vector.neg vector := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  have factor :
      2 * Coordinates3.Vector.dot vector vector / vector.quadrance = (2 : K) := by
    change 2 * vector.quadrance / vector.quadrance = (2 : K)
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * vector.quadrance * vector.quadrance⁻¹ =
          2 * (vector.quadrance * vector.quadrance⁻¹) := by ring1
      _ = 2 := by rw [cancel, mul_one]
  rw [rowMul_reflection, factor]
  ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.scale Coordinates3.Vector.neg <;> ring1

/-- Theorem 15.3: a vector is fixed by the reflection precisely when it is perpendicular to the normal. -/
theorem rowMul_reflection_eq_iff_perpendicular (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K) :
    Matrix3.rowMul other (reflection vector nonNull) = other ↔
      Coordinates3.Vector.Perpendicular other vector := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  have reflectedDot :
      Coordinates3.Vector.dot (Matrix3.rowMul other (reflection vector nonNull)) vector =
        -Coordinates3.Vector.dot other vector := by
    rw [rowMul_reflection]
    calc
      Coordinates3.Vector.dot
          (Coordinates3.Vector.sub other
            (Coordinates3.Vector.scale
              (2 * Coordinates3.Vector.dot other vector / vector.quadrance) vector))
          vector =
        Coordinates3.Vector.dot other vector -
          (2 * Coordinates3.Vector.dot other vector / vector.quadrance) *
            vector.quadrance := by
              unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot Coordinates3.Vector.sub
                Coordinates3.Vector.scale
              ring1
      _ = Coordinates3.Vector.dot other vector -
          2 * Coordinates3.Vector.dot other vector *
            (vector.quadrance * vector.quadrance⁻¹) := by
            simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
            ring1
      _ = -Coordinates3.Vector.dot other vector := by rw [cancel]; ring1
  constructor
  · intro fixed
    have equalDots := congrArg (fun value => Coordinates3.Vector.dot value vector) fixed
    rw [reflectedDot] at equalDots
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) (value : K) (twiceZero :
      2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero
      value twiceZero : value = 0)) twoNonzero
    calc
      2 * Coordinates3.Vector.dot other vector =
          Coordinates3.Vector.dot other vector - (-Coordinates3.Vector.dot other vector) := by ring1
      _ = 0 := by rw [equalDots]; ring1
  · intro perpendicular
    unfold Coordinates3.Vector.Perpendicular at perpendicular
    rw [rowMul_reflection, perpendicular, mul_zero,
      Algebra.Field.ExplicitField.zero_div]
    unfold Coordinates3.Vector.sub Coordinates3.Vector.scale
    ext <;> ring1

/-- Theorem 15.4: reflection is orthogonal. -/
theorem reflection_isOrthogonal (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.IsOrthogonal (reflection vector nonNull) := by
  unfold Matrix3.IsOrthogonal
  rw [reflection_transpose, reflection_square]

/-- The dot-product part of Theorem 15.4. -/
theorem dot_rowMul_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (first second : Vector K) :
    Coordinates3.Vector.dot (Matrix3.rowMul first (reflection vector nonNull))
        (Matrix3.rowMul second (reflection vector nonNull)) =
      Coordinates3.Vector.dot first second := by
  have coefficient := Purelib.Geometry.Rotations.Reflection.reflection_coefficient vector nonNull
  rw [rowMul_reflection, rowMul_reflection]
  calc
    Coordinates3.Vector.dot
        (Coordinates3.Vector.sub first
          (Coordinates3.Vector.scale
            (2 * Coordinates3.Vector.dot first vector / vector.quadrance) vector))
        (Coordinates3.Vector.sub second
          (Coordinates3.Vector.scale
            (2 * Coordinates3.Vector.dot second vector / vector.quadrance) vector)) =
      Coordinates3.Vector.dot first second +
        ((2 / vector.quadrance) ^ 2 * vector.quadrance -
          2 * (2 / vector.quadrance)) *
          Coordinates3.Vector.dot first vector * Coordinates3.Vector.dot second vector := by
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot Coordinates3.Vector.sub
              Coordinates3.Vector.scale
            simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
            ring1
    _ = Coordinates3.Vector.dot first second := by rw [coefficient]; ring1

/-- Theorem 15.5: a reflection has determinant minus one, proved by direct coordinate expansion rather than a basis
extension. -/
theorem determinant_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.determinant (reflection vector nonNull) = -1 := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  unfold Matrix3.determinant reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    _ = 1 - 2 * (vector.quadrance * vector.quadrance⁻¹) := by
      unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
      ring1
    _ = -1 := by rw [cancel]; ring1

/-- The reflection depends only on the nonzero scalar class of its normal. -/
theorem reflection_scale (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (nonNull : vector.quadrance ≠ 0) :
    reflection (Coordinates3.Vector.scale scalar vector)
        (Coordinates3.Vector.quadrance_scale_ne_zero scalar vector scalarNonzero nonNull) =
      reflection vector nonNull := by
  have scalarSquareNonzero : scalar ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  have scaledDenominatorNonzero :
      scalar ^ 2 * vector.quadrance ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero scalarSquareNonzero nonNull
  have ratio :
      (2 * scalar ^ 2) / (scalar ^ 2 * vector.quadrance) =
        2 / vector.quadrance := by
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {leftNumerator rightNumerator leftDenominator
      rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0) (crossProduct :
      leftNumerator * rightDenominator = rightNumerator * leftDenominator) =>
      (Purelib.Algebra.Field.Inverse.div_eq_div_of_cross_mul (K := K) (leftNumerator := leftNumerator) (rightNumerator
      := rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero
      rightNonzero crossProduct : leftNumerator / leftDenominator = rightNumerator / rightDenominator))
      scaledDenominatorNonzero nonNull
    ring1
  have coefficient :
      2 / (scalar ^ 2 * vector.quadrance) * scalar ^ 2 =
        2 / vector.quadrance := by
    calc
      2 / (scalar ^ 2 * vector.quadrance) * scalar ^ 2 =
          (2 * scalar ^ 2) / (scalar ^ 2 * vector.quadrance) := by
            simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
            ring1
      _ = 2 / vector.quadrance := ratio
  unfold reflection
  rw [Coordinates3.Vector.quadrance_scale, Matrix3.outer_scale_both,
    Matrix3.scale_scale, coefficient]

/-- Definition 16: the half turn about a non-null line. -/
def halfTurn (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    Matrix3 K := Matrix3.neg (reflection vector nonNull)

/-- A half turn depends only on the nonzero scalar class of its axis. -/
theorem halfTurn_scale (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (nonNull : vector.quadrance ≠ 0) :
    halfTurn (Coordinates3.Vector.scale scalar vector)
        (Coordinates3.Vector.quadrance_scale_ne_zero scalar vector scalarNonzero nonNull) =
      halfTurn vector nonNull := by
  unfold halfTurn
  rw [reflection_scale scalar vector scalarNonzero nonNull]

/-- Theorem 17: a half turn fixes its axis vector. -/
theorem rowMul_self_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.rowMul vector (halfTurn vector nonNull) = vector := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg, rowMul_self_reflection]
  ext <;> unfold Coordinates3.Vector.neg <;> ring1

/-- Theorem 17: a half turn negates each perpendicular vector. -/
theorem rowMul_halfTurn_of_perpendicular (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K) (perpendicular : other.Perpendicular vector) :
    Matrix3.rowMul other (halfTurn vector nonNull) = Coordinates3.Vector.neg other := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg,
    (rowMul_reflection_eq_iff_perpendicular vector nonNull twoNonzero other).2
      perpendicular]

/-- Theorem 17: a half turn is an involution. -/
theorem halfTurn_square (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.mul (halfTurn vector nonNull) (halfTurn vector nonNull) =
      Matrix3.identity := by
  unfold halfTurn
  rw [Matrix3.mul_neg_neg, reflection_square]

/-- Theorem 17: a half turn lies in `SO(3)`. -/
theorem halfTurn_isSpecialOrthogonal (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.IsSpecialOrthogonal (halfTurn vector nonNull) := by
  constructor
  · unfold Matrix3.IsOrthogonal halfTurn
    rw [Matrix3.transpose_neg, reflection_transpose,
      Matrix3.mul_neg_neg, reflection_square]
  · unfold halfTurn
    rw [Matrix3.determinant_neg, determinant_reflection]
    ring1

/-- The half turn bundled with its executable `SO(3)` certificates. -/
def halfTurnRotation (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    Rotation K where
  matrix := halfTurn vector nonNull
  orthogonal := (halfTurn_isSpecialOrthogonal vector nonNull).1
  determinantOne := (halfTurn_isSpecialOrthogonal vector nonNull).2

/-- The converse half of Theorem 18: a product of two reflections is a rotation. The direct factorization is proved
later in the paper from the anchor of an arbitrary rotation. -/
theorem reflection_product_isSpecialOrthogonal
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.IsSpecialOrthogonal
      (Matrix3.mul (reflection first firstNonNull)
        (reflection second secondNonNull)) := by
  constructor
  · exact Matrix3.isOrthogonal_mul
      (reflection_isOrthogonal first firstNonNull)
      (reflection_isOrthogonal second secondNonNull)
  · rw [Matrix3.determinant_mul, determinant_reflection,
      determinant_reflection]
    ring1

/-- The product of two reflections bundled as a rotation. -/
def reflectionProductRotation
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) : Rotation K where
  matrix := Matrix3.mul (reflection first firstNonNull)
    (reflection second secondNonNull)
  orthogonal := (reflection_product_isSpecialOrthogonal first second
    firstNonNull secondNonNull).1
  determinantOne := (reflection_product_isSpecialOrthogonal first second
    firstNonNull secondNonNull).2

/-- Theorem 19: the cross-product axis is fixed by the composition of its two reflections. -/
theorem rowMul_cross_reflection_product
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul (Coordinates3.Vector.cross first second)
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      Coordinates3.Vector.cross first second := by
  rw [← Matrix3.rowMul_mul]
  have firstPerpendicular :
      (Coordinates3.Vector.cross first second).Perpendicular first :=
    Coordinates3.Vector.cross_dot_left first second
  have secondPerpendicular :
      (Coordinates3.Vector.cross first second).Perpendicular second :=
    Coordinates3.Vector.cross_dot_right first second
  rw [(rowMul_reflection_eq_iff_perpendicular first firstNonNull twoNonzero
      (Coordinates3.Vector.cross first second)).2 firstPerpendicular,
    (rowMul_reflection_eq_iff_perpendicular second secondNonNull twoNonzero
      (Coordinates3.Vector.cross first second)).2 secondPerpendicular]

end Purelib.Geometry.Rotations.Reflection
