module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector

public import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
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

namespace Purelib.Geometry.Rotations.Cayley.Cap

open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The scalar denominator controlling whether an anchor has a cap. -/
def capDenominator (vector : Vector K) : K := 1 + vector.quadrance

/-- Lemma 22's executable inverse candidate for `I-A`. -/
def anchorResolventInverse (vector : Vector K)
    (_defined : capDenominator vector ≠ 0) : Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (1 / capDenominator vector)
      (Matrix3.add (anchor vector)
        (Matrix3.mul (anchor vector) (anchor vector))))

/-- Construct the Cayley cap matrix of an admissible anchor vector.

The stored quadratic formula is `I + (2 / (1 + Q(v))) (A + A²)`, where `A` is the anchor matrix and the supplied
certificate excludes a zero denominator (Definition 21 and Theorem 23). -/
def cap (vector : Vector K) (_defined : capDenominator vector ≠ 0) :
    Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (2 / capDenominator vector)
      (Matrix3.add (anchor vector)
        (Matrix3.mul (anchor vector) (anchor vector))))

/-- The nonzero cap denominator cancels with its explicit inverse. -/
private theorem denominator_mul_inverse (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    capDenominator vector * (capDenominator vector)⁻¹ = (1 : K) :=
  Algebra.Field.ExplicitField.mul_inv_cancel (capDenominator vector) defined

/-- Lemma 22, left-inverse certificate. -/
theorem anchorResolventInverse_left (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.identity := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have coefficientZero :
      capDenominator vector * (capDenominator vector)⁻¹ - 1 = 0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (capDenominator vector * (capDenominator vector)⁻¹ - 1)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse capDenominator Matrix3.mul
              Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity anchor
              Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
              simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact Purelib.LinearAlgebra.Coordinates3.Matrix3.zero_scale_add_identity (anchor vector)

/-- Lemma 22, right-inverse certificate. -/
theorem anchorResolventInverse_right (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (anchorResolventInverse vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.identity := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have coefficientZero :
      capDenominator vector * (capDenominator vector)⁻¹ - 1 = 0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul
        (anchorResolventInverse vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (capDenominator vector * (capDenominator vector)⁻¹ - 1)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse capDenominator Matrix3.mul
              Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity anchor
              Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
              simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact Purelib.LinearAlgebra.Coordinates3.Matrix3.zero_scale_add_identity (anchor vector)

/-- Definition 21 agrees with the cached quadratic value: the cap is the displayed Cayley product `(I+A)(I-A)⁻¹`. -/
theorem cap_eq_cayley (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.mul (Matrix3.add Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have coefficientZero :
      1 - capDenominator vector * (capDenominator vector)⁻¹ = 0 := by
    rw [cancel]
    ring1
  symm
  calc
    Matrix3.mul (Matrix3.add Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.add (cap vector defined)
        (Matrix3.scale
          (1 - capDenominator vector * (capDenominator vector)⁻¹)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse cap capDenominator
              Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity anchor Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
              simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = cap vector defined := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale <;> ring1

/-- Theorem 23: the quadratic reduction is the executable definition of the cap. -/
theorem cap_quadratic (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / capDenominator vector)
          (Matrix3.add (anchor vector)
            (Matrix3.mul (anchor vector) (anchor vector)))) := rfl

/-- The coordinate matrix printed after Theorem 23. -/
theorem cap_coordinate_formula (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.scale (1 / capDenominator vector)
        ⟨vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2 + 1,
          2 * (vector.s + vector.r * vector.t),
          2 * (-vector.r + vector.s * vector.t),
          2 * (-vector.s + vector.r * vector.t),
          -vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 + 1,
          2 * (vector.t + vector.r * vector.s),
          2 * (vector.r + vector.s * vector.t),
          2 * (-vector.t + vector.r * vector.s),
          -vector.t ^ 2 - vector.r ^ 2 + vector.s ^ 2 + 1⟩ := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have inverseCancel :
      capDenominator vector * (1 / capDenominator vector) = 1 := by
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      capDenominator vector * (1 * (capDenominator vector)⁻¹) =
          capDenominator vector * (capDenominator vector)⁻¹ := by ring1
      _ = 1 := cancel
  have doubleCancel :
      capDenominator vector * (2 / capDenominator vector) = 2 := by
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      capDenominator vector * (2 * (capDenominator vector)⁻¹) =
          2 * (capDenominator vector * (capDenominator vector)⁻¹) := by
            ring1
      _ = 2 := by rw [cancel]; ring1
  apply Matrix3.eq_of_scale_eq_scale defined
  unfold cap
  rw [Matrix3.scale_add, Matrix3.scale_scale, doubleCancel,
    Matrix3.scale_scale, inverseCancel]
  ext <;> unfold capDenominator Matrix3.add Matrix3.scale Matrix3.identity
    Matrix3.mul anchor Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;> ring1

/-- The determinant calculation preceding Lemma 22. -/
theorem determinant_identity_sub_anchor (vector : Vector K) :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (anchor vector)) =
      capDenominator vector := by
  unfold Matrix3.determinant Matrix3.sub Matrix3.identity anchor
    capDenominator Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  ring1

/-- The matching determinant for `I+A`. -/
theorem determinant_identity_add_anchor (vector : Vector K) :
    Matrix3.determinant (Matrix3.add Matrix3.identity (anchor vector)) =
      capDenominator vector := by
  unfold Matrix3.determinant Matrix3.add Matrix3.identity anchor
    capDenominator Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  ring1

/-- Multiplying the quadratic cap by `I-A` recovers `I+A`. -/
theorem cap_mul_identity_sub_anchor (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (cap vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add Matrix3.identity (anchor vector) := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have coefficientZero :
      2 * (capDenominator vector * (capDenominator vector)⁻¹ - 1) =
        0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul (cap vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add (Matrix3.add Matrix3.identity (anchor vector))
        (Matrix3.scale
          (2 * (capDenominator vector *
            (capDenominator vector)⁻¹ - 1)) (anchor vector)) := by
              ext <;> unfold cap capDenominator Matrix3.mul Matrix3.sub
                Matrix3.add Matrix3.scale Matrix3.identity anchor
                Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
                simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.add Matrix3.identity (anchor vector) := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity anchor <;>
        ring1

/-- The same Cayley relation with `I-A` on the left. -/
theorem identity_sub_anchor_mul_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
        (cap vector defined) =
      Matrix3.add Matrix3.identity (anchor vector) := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  have coefficientZero :
      2 * (capDenominator vector * (capDenominator vector)⁻¹ - 1) =
        0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
        (cap vector defined) =
      Matrix3.add (Matrix3.add Matrix3.identity (anchor vector))
        (Matrix3.scale
          (2 * (capDenominator vector *
            (capDenominator vector)⁻¹ - 1)) (anchor vector)) := by
              ext <;> unfold cap capDenominator Matrix3.mul Matrix3.sub
                Matrix3.add Matrix3.scale Matrix3.identity anchor
                Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
                simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.add Matrix3.identity (anchor vector) := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity anchor <;>
        ring1

/-- Negating the anchor leaves the cap denominator unchanged. -/
theorem capDenominator_neg (vector : Vector K) :
    capDenominator (Coordinates3.Vector.neg vector) = capDenominator vector := by
  unfold capDenominator
  rw [Coordinates3.Vector.quadrance_neg]

/-- The negated anchor is in the cap domain whenever the original anchor is. -/
theorem cap_neg_defined (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    capDenominator (Coordinates3.Vector.neg vector) ≠ 0 := by
  rw [capDenominator_neg]
  exact defined

/-- Transposition negates the anchor vector of a cap. -/
theorem transpose_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.transpose (cap vector defined) =
      cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined) := by
  unfold cap
  rw [capDenominator_neg, anchor_neg]
  ext <;> unfold Matrix3.transpose Matrix3.add Matrix3.scale
    Matrix3.identity Matrix3.mul Matrix3.neg anchor <;> ring1

/-- The scalar remainder in the product of opposite-anchor caps vanishes. -/
private theorem cap_inverse_coefficient (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    2 * (2 / capDenominator vector) -
      (2 / capDenominator vector) ^ 2 * capDenominator vector = 0 := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    2 * (2 * (capDenominator vector)⁻¹) -
        (2 * (capDenominator vector)⁻¹) ^ 2 *
          capDenominator vector =
      4 * (capDenominator vector)⁻¹ *
        (1 - capDenominator vector * (capDenominator vector)⁻¹) := by
          ring1
    _ = 0 := by rw [cancel]; ring1

/-- A cap multiplied by the cap at the negated anchor is the identity. -/
theorem cap_mul_cap_neg (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (cap vector defined)
        (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined)) =
      Matrix3.identity := by
  have coefficientZero := Purelib.Geometry.Rotations.Cayley.Cap.cap_inverse_coefficient vector defined
  calc
    Matrix3.mul (cap vector defined)
        (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined)) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (2 * (2 / capDenominator vector) -
            (2 / capDenominator vector) ^ 2 * capDenominator vector)
          (Matrix3.mul (anchor vector) (anchor vector))) := by
            unfold cap
            rw [capDenominator_neg, anchor_neg]
            ext <;> unfold Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity Matrix3.neg anchor capDenominator
              Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact Purelib.LinearAlgebra.Coordinates3.Matrix3.zero_scale_add_identity _

/-- The inverse multiplication in the opposite order. -/
theorem cap_neg_mul_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined))
        (cap vector defined) = Matrix3.identity := by
  have coefficientZero := Purelib.Geometry.Rotations.Cayley.Cap.cap_inverse_coefficient vector defined
  calc
    Matrix3.mul
        (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined))
        (cap vector defined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (2 * (2 / capDenominator vector) -
            (2 / capDenominator vector) ^ 2 * capDenominator vector)
          (Matrix3.mul (anchor vector) (anchor vector))) := by
            unfold cap
            rw [capDenominator_neg, anchor_neg]
            ext <;> unfold Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity Matrix3.neg anchor capDenominator
              Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact Purelib.LinearAlgebra.Coordinates3.Matrix3.zero_scale_add_identity _

/-- Theorem 24.1, orthogonality of a cap. -/
theorem cap_isOrthogonal (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.IsOrthogonal (cap vector defined) := by
  unfold Matrix3.IsOrthogonal
  rw [transpose_cap, cap_mul_cap_neg]

/-- Theorem 24.1, determinant one. -/
theorem determinant_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.determinant (cap vector defined) = 1 := by
  have determinantEquation := congrArg Matrix3.determinant
    (cap_mul_identity_sub_anchor vector defined)
  rw [Matrix3.determinant_mul, determinant_identity_sub_anchor,
    determinant_identity_add_anchor] at determinantEquation
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  calc
    Matrix3.determinant (cap vector defined) =
        Matrix3.determinant (cap vector defined) *
          (capDenominator vector * (capDenominator vector)⁻¹) := by
            rw [cancel, mul_one]
    _ = (Matrix3.determinant (cap vector defined) *
          capDenominator vector) * (capDenominator vector)⁻¹ := by ring1
    _ = capDenominator vector * (capDenominator vector)⁻¹ := by
      rw [determinantEquation]
    _ = 1 := cancel

/-- The cap bundled with its executable `SO(3)` certificates. -/
def capRotation (vector : Vector K) (defined : capDenominator vector ≠ 0) :
    Rotation K where
  matrix := cap vector defined
  orthogonal := cap_isOrthogonal vector defined
  determinantOne := determinant_cap vector defined

/-- Theorem 24.2: the anchor vector is fixed by its cap. -/
theorem rowMul_self_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.rowMul vector (cap vector defined) = vector := by
  ext <;> unfold Matrix3.rowMul cap capDenominator Matrix3.add
    Matrix3.scale Matrix3.identity Matrix3.mul anchor Coordinates3.Vector.quadrance
    Coordinates3.Vector.dot <;> ring1

/-- A cap fixes exactly the vectors in the kernel of its original anchor.

The cap denominator and nonzero two allow its Cayley relation to recover the same anchor kernel. -/
theorem rowMul_cap_eq_self_iff_anchor_kernel (vector other : Vector K)
    (defined : capDenominator vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul other (cap vector defined) = other ↔
      Matrix3.rowMul other (anchor vector) = Vector3.zero := by
  constructor
  · intro fixed
    have transported := congrArg
      (fun value => Matrix3.rowMul value (Matrix3.sub Matrix3.identity (anchor vector))) fixed
    rw [Matrix3.rowMul_mul, cap_mul_identity_sub_anchor,
      Matrix3.rowMul_add, Matrix3.rowMul_sub, Matrix3.rowMul_identity] at transported
    let kernelValue := Matrix3.rowMul other (anchor vector)
    have shifted := congrArg (fun value => Vector3.sub value other) transported
    have negative : kernelValue = Vector3.neg kernelValue := by
      calc
        kernelValue = Vector3.sub (Vector3.add other kernelValue) other := by
          ext <;> unfold Vector3.sub Vector3.add <;> ring1
        _ = Vector3.sub (Vector3.sub other kernelValue) other := shifted
        _ = Vector3.neg kernelValue := by
          ext <;> unfold Vector3.sub Vector3.neg <;> ring1
    exact Vector3.eq_zero_of_eq_neg kernelValue twoNonzero negative
  · intro kernel
    have zeroAction : Matrix3.rowMul Vector3.zero (anchor vector) = Vector3.zero := by
      ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1
    rw [cap, Matrix3.rowMul_add, Matrix3.rowMul_identity, Matrix3.rowMul_scale,
      Matrix3.rowMul_add, ← Matrix3.rowMul_mul, kernel, zeroAction,
      Vector3.zero_add, Vector3.scale_zero, Vector3.add_zero]

/-- The fixed vectors of a cap with non-null anchor are exactly their projections onto its anchor line.

The projection coefficient uses the original anchor quadrance; no auxiliary eigenvector or basis is selected. -/
theorem rowMul_cap_eq_self_iff_projection (vector other : Vector K)
    (defined : capDenominator vector ≠ 0) (nonNull : vector.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul other (cap vector defined) = other ↔
      other = Vector3.scale (other.dot vector / vector.quadrance) vector := by
  constructor
  · intro fixed
    have kernel := (rowMul_cap_eq_self_iff_anchor_kernel vector other defined twoNonzero).mp fixed
    have squared := congrArg (fun value => Matrix3.rowMul value (anchor vector)) kernel
    rw [Matrix3.rowMul_mul, anchor_square, Matrix3.rowMul_sub,
      Matrix3.rowMul_outer, Matrix3.rowMul_scale, Matrix3.rowMul_identity] at squared
    have zeroAction : Matrix3.rowMul Vector3.zero (anchor vector) = Vector3.zero := by
      ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1
    rw [zeroAction] at squared
    have scaled : Vector3.scale vector.quadrance other = Vector3.scale (other.dot vector) vector := by
      have shifted := congrArg (fun value => Vector3.add value (Vector3.scale vector.quadrance other)) squared
      calc
        Vector3.scale vector.quadrance other = Vector3.add Vector3.zero
            (Vector3.scale vector.quadrance other) := (Vector3.zero_add _).symm
        _ = Vector3.add (Vector3.sub (Vector3.scale (other.dot vector) vector)
            (Vector3.scale vector.quadrance other)) (Vector3.scale vector.quadrance other) := shifted.symm
        _ = Vector3.scale (other.dot vector) vector := by
          ext <;> unfold Vector3.add Vector3.sub <;> ring1
    have cancel : vector.quadrance⁻¹ * vector.quadrance = 1 := by
      rw [mul_comm]
      exact Algebra.Field.ExplicitField.mul_inv_cancel vector.quadrance nonNull
    calc
      other = Vector3.scale vector.quadrance⁻¹ (Vector3.scale vector.quadrance other) := by
        rw [Vector3.scale_scale, cancel, Vector3.one_scale]
      _ = Vector3.scale vector.quadrance⁻¹ (Vector3.scale (other.dot vector) vector) :=
        congrArg (Vector3.scale vector.quadrance⁻¹) scaled
      _ = Vector3.scale (other.dot vector / vector.quadrance) vector := by
        rw [Vector3.scale_scale, Algebra.Field.ExplicitField.div_eq_mul_inv, mul_comm]
  · intro projected
    calc
      Matrix3.rowMul other (cap vector defined) =
          Matrix3.rowMul (Vector3.scale (other.dot vector / vector.quadrance) vector) (cap vector defined) :=
        congrArg (fun value => Matrix3.rowMul value (cap vector defined)) projected
      _ = Vector3.scale (other.dot vector / vector.quadrance) vector := by
        rw [Matrix3.rowMul_vector_scale, rowMul_self_cap]
      _ = other := projected.symm

/-- Trace calculation used in Theorem 24.3. -/
theorem trace_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.trace (cap vector defined) =
      (3 - vector.quadrance) / capDenominator vector := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    Matrix3.trace (cap vector defined) =
        3 - 4 * vector.quadrance * (capDenominator vector)⁻¹ := by
          unfold Matrix3.trace cap capDenominator Matrix3.add Matrix3.scale
            Matrix3.identity Matrix3.mul anchor Coordinates3.Vector.quadrance Coordinates3.Vector.dot
          simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
          ring1
    _ = 3 * (capDenominator vector * (capDenominator vector)⁻¹) -
        4 * vector.quadrance * (capDenominator vector)⁻¹ := by
          rw [cancel]
          ring1
    _ = (3 - vector.quadrance) * (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- The adjugate of a cap is its transpose, obtained from the explicit left inverse rather than a generic inverse
theorem. -/
theorem adjugate_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.adjugate (cap vector defined) =
      Matrix3.transpose (cap vector defined) := by
  have adjugateProduct :
      Matrix3.mul (cap vector defined) (Matrix3.adjugate (cap vector defined)) =
        Matrix3.identity := by
    calc
      Matrix3.mul (cap vector defined) (Matrix3.adjugate (cap vector defined)) =
          Matrix3.scale (Matrix3.determinant (cap vector defined))
            Matrix3.identity := Matrix3.mul_adjugate _
      _ = Matrix3.identity := by
        rw [determinant_cap]
        ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1
  calc
    Matrix3.adjugate (cap vector defined) =
        Matrix3.mul Matrix3.identity (Matrix3.adjugate (cap vector defined)) := by
          rw [Matrix3.identity_mul]
    _ = Matrix3.mul
        (Matrix3.mul
          (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined))
          (cap vector defined))
        (Matrix3.adjugate (cap vector defined)) := by
          rw [cap_neg_mul_cap]
    _ = Matrix3.mul
        (cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined))
        (Matrix3.mul (cap vector defined)
          (Matrix3.adjugate (cap vector defined))) := by
            rw [Matrix3.mul_assoc]
    _ = cap (Coordinates3.Vector.neg vector) (cap_neg_defined vector defined) := by
      rw [adjugateProduct, Matrix3.mul_identity]
    _ = Matrix3.transpose (cap vector defined) :=
      (transpose_cap vector defined).symm

/-- For a cap, the two non-leading characteristic coefficients agree. -/
theorem principalTrace_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.principalTrace (cap vector defined) =
      Matrix3.trace (cap vector defined) := by
  unfold Matrix3.principalTrace
  rw [adjugate_cap, Matrix3.trace_transpose]

/-- The cap trace minus one is `2(1-Q)/(1+Q)`. -/
private theorem trace_cap_sub_one (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.trace (cap vector defined) - 1 =
      2 * (1 - vector.quadrance) / capDenominator vector := by
  have cancel := Purelib.Geometry.Rotations.Cayley.Cap.denominator_mul_inverse vector defined
  rw [trace_cap]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (3 - vector.quadrance) * (capDenominator vector)⁻¹ - 1 =
        (3 - vector.quadrance) * (capDenominator vector)⁻¹ -
          capDenominator vector * (capDenominator vector)⁻¹ := by
            rw [cancel]
    _ = 2 * (1 - vector.quadrance) *
        (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 24.3: characteristic polynomial of a cap. -/
theorem characteristicValue_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) (X : K) :
    Matrix3.characteristicValue (cap vector defined) X =
      (X - 1) *
        (X ^ 2 -
          (2 * (1 - vector.quadrance) / capDenominator vector) * X + 1) := by
  calc
    Matrix3.characteristicValue (cap vector defined) X =
        X ^ 3 - Matrix3.trace (cap vector defined) * X ^ 2 +
          Matrix3.principalTrace (cap vector defined) * X -
            Matrix3.determinant (cap vector defined) :=
      Matrix3.characteristicValue_expansion _ _
    _ = X ^ 3 - Matrix3.trace (cap vector defined) * X ^ 2 +
          Matrix3.trace (cap vector defined) * X - 1 := by
      rw [principalTrace_cap, determinant_cap]
    _ = (X - 1) *
        (X ^ 2 - (Matrix3.trace (cap vector defined) - 1) * X + 1) := by
      ring1
    _ = (X - 1) *
        (X ^ 2 -
          (2 * (1 - vector.quadrance) / capDenominator vector) * X + 1) := by
      rw [Purelib.Geometry.Rotations.Cayley.Cap.trace_cap_sub_one]

/-- Theorem 24.4: minus one is not an eigenvalue of a cap. -/
theorem rowMul_cap_eq_neg_implies_zero (vector : Vector K)
    (defined : capDenominator vector ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K)
    (negativeEigen : Matrix3.rowMul other (cap vector defined) =
      Coordinates3.Vector.neg other) : other = Coordinates3.Vector.zero := by
  have transported := congrArg
    (fun value => Matrix3.rowMul value
      (Matrix3.sub Matrix3.identity (anchor vector))) negativeEigen
  rw [Matrix3.rowMul_mul, cap_mul_identity_sub_anchor] at transported
  have tEquation := congrArg Coordinates3.Vector.t transported
  have rEquation := congrArg Coordinates3.Vector.r transported
  have sEquation := congrArg Coordinates3.Vector.s transported
  apply Coordinates3.Vector.ext
  · apply Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.t =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).t -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Coordinates3.Vector.neg
              ring1
      _ = (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t := by
              rw [tEquation]
      _ = 0 := by ring1
  · apply Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.r =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).r -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Coordinates3.Vector.neg
              ring1
      _ = (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r := by
              rw [rEquation]
      _ = 0 := by ring1
  · apply Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.s =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).s -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Coordinates3.Vector.neg
              ring1
      _ = (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s -
          (Matrix3.rowMul (Coordinates3.Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s := by
              rw [sEquation]
      _ = 0 := by ring1

/-- The antisymmetric part of a cap exposes its anchor up to the displayed nonzero scalar. -/
theorem cap_antisymmetric_part (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.sub (cap vector defined) (Matrix3.transpose (cap vector defined)) =
      Matrix3.scale (4 / capDenominator vector) (anchor vector) := by
  ext <;> unfold cap capDenominator Matrix3.sub Matrix3.transpose
    Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul anchor
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1

/-- Theorem 24.5: the cap is injective on its domain. -/
theorem cap_injective (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstDefined : capDenominator first ≠ 0)
    (secondDefined : capDenominator second ≠ 0)
    (equalCaps : cap first firstDefined = cap second secondDefined) :
    first = second := by
  have traceEqual := congrArg Matrix3.trace equalCaps
  rw [trace_cap first firstDefined, trace_cap second secondDefined] at traceEqual
  have crossed := Purelib.Algebra.Field.Inverse.cross_mul_of_div_eq_div firstDefined secondDefined traceEqual
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have quadranceDifference :
      4 * (second.quadrance - first.quadrance) = 0 := by
    calc
      4 * (second.quadrance - first.quadrance) =
          (3 - first.quadrance) * capDenominator second -
            (3 - second.quadrance) * capDenominator first := by
              unfold capDenominator
              ring1
      _ = 0 := by rw [crossed]; ring1
  have differenceZero := Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
    fourNonzero quadranceDifference
  have quadrancesEqual : first.quadrance = second.quadrance := by
    calc
      first.quadrance = second.quadrance -
          (second.quadrance - first.quadrance) := by ring1
      _ = second.quadrance := by rw [differenceZero]; ring1
  have partsEqual := congrArg
    (fun matrix => Matrix3.sub matrix (Matrix3.transpose matrix)) equalCaps
  rw [cap_antisymmetric_part first firstDefined,
    cap_antisymmetric_part second secondDefined] at partsEqual
  have denominatorsEqual : capDenominator first = capDenominator second := by
    unfold capDenominator
    rw [quadrancesEqual]
  rw [denominatorsEqual] at partsEqual
  have scalarNonzero : 4 / capDenominator second ≠ 0 :=
    Algebra.Field.ExplicitField.div_ne_zero fourNonzero secondDefined
  exact anchor_injective
    (Matrix3.eq_of_scale_eq_scale scalarNonzero partsEqual)

end Purelib.Geometry.Rotations.Cayley.Cap

section
public section
namespace Purelib.Geometry.Rotations.Cayley.Cap

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Equal anchor vectors yield equal caps with their supplied domain certificates. -/
public theorem cap_congr_vector {first second :
  Coordinates3.Vector K}
    (equal : first = second)
    (firstDefined : Cap.capDenominator first ≠ 0)
    (secondDefined : Cap.capDenominator second ≠ 0) :
    Cap.cap first firstDefined = Cap.cap second secondDefined := by
  subst second
  rfl

end Purelib.Geometry.Rotations.Cayley.Cap
end

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Cayley
namespace Purelib.Geometry.Rotations.Cayley.Cap
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Equal anchor vectors give equal cap matrices regardless of nonzero-denominator proofs. -/
public theorem eq_of_vector_eq {left right : Coordinates3.Vector K}
    (equal : left = right) (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0) :
    Cap.cap left leftDefined = Cap.cap right rightDefined := by
  subst right
  rfl

end Purelib.Geometry.Rotations.Cayley.Cap
end
