module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Basic
public import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.Geometry.Rotations.Ternary.Reflection

import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector

import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Reflection
import Purelib.Geometry.Rotations.Cayley.Cap
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Geometry.Quadratic.Ternary.Reflection
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Clifford.TernaryForm

open Purelib.LinearAlgebra

@[expose] public section

/-!
# Cayley caps and spreads for displayed ternary forms

This module recovers the affine anchor chart of the Euclidean rotation theory
for an arbitrary displayed symmetric nondegenerate ternary form.  The form
discriminant is visible in every formula: the affine Clifford representative
`(1, u)` has reduced norm `1 + det(M) Q_M(u)`, and the scalar coordinate of
the product of two such representatives is
`1 - det(M) B_M(u, v)`.

All constructions use the already displayed even Clifford coordinates.  No
basis change, diagonalization, quotient representative, or choice principle
is involved.
-/

section
namespace Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.TwoHalfTurnFactorization
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Ternary.Cayley
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Reflection
open Purelib.Geometry.Rotations.Cayley.Cap
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The first factorization axis is perpendicular to the vector coordinate of the resulting Clifford representative. -/
public theorem
  firstAxis_perpendicular_cliffordPreimage
    {form : Ternary.Basic.TernaryForm K} {rotation : form.SpecialOrthogonal}
    (factorization : TernaryForm.TwoHalfTurnFactorization form rotation) :
    form.Perpendicular factorization.firstAxis
      (TwoHalfTurnFactorization.cliffordPreimage factorization).toEvenClifford.vector := by
  have crossPerpendicular :
      form.Perpendicular factorization.firstAxis
        (form.cliffordCross factorization.firstAxis
          factorization.secondAxis) :=
    (form.perpendicular_comm _ _).2
      (form.cliffordCross_perpendicular_left
        factorization.firstAxis factorization.secondAxis)
  unfold TwoHalfTurnFactorization.cliffordPreimage
    NonNullEvenClifford.mul NonNullEvenClifford.halfTurnValue
    EvenClifford.ofVector EvenClifford.mul EvenClifford.productVector
  change form.Perpendicular factorization.firstAxis
    (Coordinates3.Vector.sub
      (Coordinates3.Vector.add
        (Coordinates3.Vector.scale 0 factorization.secondAxis)
        (Coordinates3.Vector.scale 0 factorization.firstAxis))
      (form.cliffordCross factorization.firstAxis
        factorization.secondAxis))
  unfold TernaryForm.Perpendicular
  rw [form.bilinear_sub_right, form.bilinear_add_right,
    form.bilinear_scale_right, form.bilinear_scale_right]
  rw [crossPerpendicular]
  ring1

end Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.TwoHalfTurnFactorization
end

namespace Purelib.Geometry.Rotations.Ternary.Cayley

open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Reflection
open Purelib.Geometry.Rotations.Cayley.Cap

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section TernaryForm

/-- The form-relative cap denominator. The determinant factor is forced by the reduced norm convention for the displayed
even Clifford algebra. -/
def TernaryForm.cayleyDenominator (form : Ternary.Basic.TernaryForm K) (anchor : Coordinates3.Vector K) : K :=
  1 + form.determinant * form.quadrance anchor

/-- The unnormalized affine Clifford representative `(1, anchor)`. -/
def TernaryForm.capRepresentative (form : Ternary.Basic.TernaryForm K) (anchor : Coordinates3.Vector K) :
    form.EvenClifford :=
  ⟨1, anchor⟩

/-- The scalar-one Clifford representative has norm equal to the cap denominator. -/
theorem TernaryForm.norm_capRepresentative (form : Ternary.Basic.TernaryForm K)
    (anchor : Coordinates3.Vector K) :
    (EvenClifford.norm ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) anchor)) =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor := by
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative EvenClifford.norm
    Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator
  ring1

/-- A defined form-relative Cayley cap, retaining its nonzero denominator as executable data. -/
def TernaryForm.capValue (form : Ternary.Basic.TernaryForm K) (anchor : Coordinates3.Vector K)
    (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0) :
    form.NonNullEvenClifford where
  toEvenClifford := (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) anchor
  normNonzero := by
    rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.norm_capRepresentative form)]
    exact defined

/-- The form-relative Cayley cap as a displayed special-orthogonal transformation. -/
def TernaryForm.capRotation (form : Ternary.Basic.TernaryForm K) (anchor : Coordinates3.Vector K)
    (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0) :
    form.SpecialOrthogonal :=
  (NonNullEvenClifford.actionRotation ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) anchor defined))

/-- Equal anchor vectors give equal original cap rotations with their respective domain certificates. -/
theorem TernaryForm.capRotation_eq_of_anchor_eq (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K)
    (leftDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) left ≠ 0)
    (rightDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) right ≠ 0)
    (equal : left = right) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) left leftDefined =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) right rightDefined := by
  cases equal
  rfl

/-- Expand the form-relative cap action into its scalar, bilinear projection, and Clifford cross terms.

The cap denominator is nonzero; the formula uses its retained inverse. -/
theorem TernaryForm.capRotation_act (form : Ternary.Basic.TernaryForm K) (anchor : Coordinates3.Vector K)
    (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0) (vector :
      Coordinates3.Vector K) :
    (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) anchor defined).toIsometry) vector =
      Coordinates3.Vector.scale ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor)⁻¹
        (Coordinates3.Vector.add
          (Coordinates3.Vector.add
            (Coordinates3.Vector.scale
              (1 - form.determinant * form.quadrance anchor) vector)
            (Coordinates3.Vector.scale
              (2 * form.determinant * form.bilinear vector anchor) anchor))
          (Coordinates3.Vector.scale (-2) (form.cliffordCross vector anchor))) := by
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation
  rw [NonNullEvenClifford.actionRotation_act]
  unfold NonNullEvenClifford.action
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.norm_capRepresentative form)]
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative EvenClifford.actionNumerator
    Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator
  ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1

/-- Trace of a normalized Clifford action, in the determinant-scaled vector convention. -/
theorem TernaryForm.NonNullEvenClifford.trace_actionMatrix
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford) :
    Matrix3.trace (NonNullEvenClifford.actionMatrix value) =
      (EvenClifford.norm value.toEvenClifford)⁻¹ *
        (3 * value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) := by
  unfold NonNullEvenClifford.actionMatrix
  rw [Matrix3.trace_scale]
  unfold EvenClifford.actionNumeratorMatrix
  rw [Matrix3.trace_add, Matrix3.trace_add,
    Matrix3.trace_scale, Matrix3.trace_identity,
    Matrix3.trace_scale, Matrix3.trace_outer,
    Matrix3.trace_scale, form.trace_actionSkew]
  change (EvenClifford.norm value.toEvenClifford)⁻¹ *
      ((value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) * 3 +
        (2 * form.determinant) *
          form.quadrance value.toEvenClifford.vector +
        2 * value.toEvenClifford.scalar * 0) = _
  ring1

/-- The trace-defined half spread for a displayed ternary rotation. -/
def TernaryForm.rotationHalfSpread (form : Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) : K :=
  (3 - Matrix3.trace rotation.matrix) / 4

/-- The canonical spread polynomial attached to the trace-defined half spread. -/
def TernaryForm.rotationSpread (form : Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) : K :=
  4 * (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation *
    (1 - (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation)

/-- The half spread of a Clifford action is its determinant-weighted vector quadrance divided by the reduced norm. -/
theorem TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) (NonNullEvenClifford.actionRotation value) =
      form.determinant * form.quadrance value.toEvenClifford.vector /
        (EvenClifford.norm value.toEvenClifford) := by
  have normCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  have fourCancel := Algebra.Field.ExplicitField.mul_inv_cancel 4
    ((fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero)
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
  change (3 - Matrix3.trace (NonNullEvenClifford.actionMatrix value)) / 4 = _
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.trace_actionMatrix value)]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (3 - (EvenClifford.norm value.toEvenClifford)⁻¹ *
        (3 * value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector)) *
        (4 : K)⁻¹ =
      (3 * ((EvenClifford.norm value.toEvenClifford) *
          (EvenClifford.norm value.toEvenClifford)⁻¹) -
        (EvenClifford.norm value.toEvenClifford)⁻¹ *
          (3 * value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector)) *
        (4 : K)⁻¹ := by rw [normCancel]; ring1
    _ = (4 * form.determinant *
        form.quadrance value.toEvenClifford.vector *
          (EvenClifford.norm value.toEvenClifford)⁻¹) * (4 : K)⁻¹ := by
      unfold EvenClifford.norm
      ring1
    _ = form.determinant *
        form.quadrance value.toEvenClifford.vector *
          (EvenClifford.norm value.toEvenClifford)⁻¹ := by
      rw [show (4 * form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹) * (4 : K)⁻¹ =
          (form.determinant *
            form.quadrance value.toEvenClifford.vector *
              (EvenClifford.norm value.toEvenClifford)⁻¹) * (4 * (4 : K)⁻¹) by ring1,
        fourCancel, mul_one]

/-- The cap half spread is its determinant-weighted anchor quadrance divided by the cap denominator. -/
theorem TernaryForm.rotationHalfSpread_cap (form : Ternary.Basic.TernaryForm K)
    (anchor : Coordinates3.Vector K) (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form)
      anchor ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) anchor defined) =
      form.determinant * form.quadrance anchor /
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor := by
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation
  simpa only [Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue,
    Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative,
    Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator,
    EvenClifford.norm, one_pow] using
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) anchor defined))
        twoNonzero

/-! ## Geometric spread on the canonical axis -/

/-- Rotation spread evaluated on a displayed non-null test vector. Since a form rotation preserves quadrance, this is
the ordinary projective spread of the test vector and its image with the equal quadrances already cancelled. -/
def TernaryForm.rotationSpreadAt (form : Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) (vector : Coordinates3.Vector K)
    (_nonNull : form.quadrance vector ≠ 0) : K :=
  1 - (form.bilinear vector ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) vector) /
    form.quadrance vector) ^ 2

/-- Compute the bilinear pairing of a non-null vector with its Clifford image when it is perpendicular to the axis. -/
theorem TernaryForm.NonNullEvenClifford.bilinear_self_action_of_perpendicular
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector) :
    form.bilinear vector ((NonNullEvenClifford.action value) vector) =
      (EvenClifford.norm value.toEvenClifford)⁻¹ *
        (value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) *
        form.quadrance vector := by
  have pairingZero :
      form.bilinear vector value.toEvenClifford.vector = 0 :=
    perpendicular
  have crossZero :
      form.bilinear vector
        (form.cliffordCross vector value.toEvenClifford.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left
      vector value.toEvenClifford.vector
  unfold NonNullEvenClifford.action EvenClifford.actionNumerator
  rw [form.bilinear_scale_right, form.bilinear_add_right,
    form.bilinear_add_right, form.bilinear_scale_right,
    form.bilinear_scale_right, form.bilinear_scale_right,
    pairingZero, crossZero]
  unfold TernaryForm.quadrance
  ring1

/-- A non-null perpendicular vector has spread `4h(1-h)`, with `h` the determinant-weighted axis quadrance over the
Clifford norm. -/
theorem TernaryForm.NonNullEvenClifford.rotationSpreadAt_of_perpendicular
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt form) (NonNullEvenClifford.actionRotation value)
      vector nonNull =
      4 *
        (form.determinant * form.quadrance value.toEvenClifford.vector /
          (EvenClifford.norm value.toEvenClifford)) *
        (1 - form.determinant *
          form.quadrance value.toEvenClifford.vector /
            (EvenClifford.norm value.toEvenClifford)) := by
  have quadranceCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (form.quadrance vector) nonNull
  have normCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  have split :
      value.toEvenClifford.scalar ^ 2 *
          (EvenClifford.norm value.toEvenClifford)⁻¹ +
        form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹ = 1 := by
    calc
      value.toEvenClifford.scalar ^ 2 *
            (EvenClifford.norm value.toEvenClifford)⁻¹ +
          form.determinant *
            form.quadrance value.toEvenClifford.vector *
              (EvenClifford.norm value.toEvenClifford)⁻¹ =
        (EvenClifford.norm value.toEvenClifford) * (EvenClifford.norm value.toEvenClifford)⁻¹ := by
          unfold EvenClifford.norm
          ring1
      _ = 1 := normCancel
  have complement :
      1 - form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹ =
        value.toEvenClifford.scalar ^ 2 *
          (EvenClifford.norm value.toEvenClifford)⁻¹ := by
    rw [← split]
    ring1
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt
  rw [NonNullEvenClifford.actionRotation_act,
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.bilinear_self_action_of_perpendicular value)
      vector perpendicular]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  have quotient :
      ((EvenClifford.norm value.toEvenClifford)⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) *
          form.quadrance vector) *
          (form.quadrance vector)⁻¹ =
        (EvenClifford.norm value.toEvenClifford)⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) := by
    calc
      ((EvenClifford.norm value.toEvenClifford)⁻¹ *
            (value.toEvenClifford.scalar ^ 2 -
              form.determinant *
                form.quadrance value.toEvenClifford.vector) *
            form.quadrance vector) *
            (form.quadrance vector)⁻¹ =
        (EvenClifford.norm value.toEvenClifford)⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) *
          (form.quadrance vector * (form.quadrance vector)⁻¹) := by
            ring1
      _ = _ := by rw [quadranceCancel, mul_one]
  rw [quotient]
  change
    1 - ((EvenClifford.norm value.toEvenClifford)⁻¹ *
      (value.toEvenClifford.scalar ^ 2 -
        form.determinant *
          form.quadrance value.toEvenClifford.vector)) ^ 2 = _
  calc
    1 - ((EvenClifford.norm value.toEvenClifford)⁻¹ *
        (value.toEvenClifford.scalar ^ 2 -
          form.determinant *
            form.quadrance value.toEvenClifford.vector)) ^ 2 =
      (value.toEvenClifford.scalar ^ 2 *
          (EvenClifford.norm value.toEvenClifford)⁻¹ +
        form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹) ^ 2 -
        ((EvenClifford.norm value.toEvenClifford)⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector)) ^ 2 := by
      have oneSquare :
          (1 : K) =
            (value.toEvenClifford.scalar ^ 2 *
                (EvenClifford.norm value.toEvenClifford)⁻¹ +
              form.determinant *
                form.quadrance value.toEvenClifford.vector *
                  (EvenClifford.norm value.toEvenClifford)⁻¹) ^ 2 := by
        calc
          (1 : K) = 1 ^ 2 := by ring1
          _ = (value.toEvenClifford.scalar ^ 2 *
                (EvenClifford.norm value.toEvenClifford)⁻¹ +
              form.determinant *
                form.quadrance value.toEvenClifford.vector *
                  (EvenClifford.norm value.toEvenClifford)⁻¹) ^ 2 := by rw [split]
      exact congrArg
        (fun scalar : K => scalar -
          ((EvenClifford.norm value.toEvenClifford)⁻¹ *
            (value.toEvenClifford.scalar ^ 2 -
              form.determinant *
                form.quadrance value.toEvenClifford.vector)) ^ 2)
        oneSquare
    _ =
      4 * value.toEvenClifford.scalar ^ 2 * form.determinant *
        form.quadrance value.toEvenClifford.vector *
          (EvenClifford.norm value.toEvenClifford)⁻¹ ^ 2 := by
      ring1
    _ = 4 *
        (form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹) *
        (1 - form.determinant *
          form.quadrance value.toEvenClifford.vector *
            (EvenClifford.norm value.toEvenClifford)⁻¹) := by
      rw [complement]
      ring1

/-- Every non-null vector perpendicular to the Clifford axis realizes the rotation spread when two is nonzero. -/
theorem TernaryForm.NonNullEvenClifford.rotationSpreadAt_eq_rotationSpread
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt form) (NonNullEvenClifford.actionRotation value)
      vector nonNull =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpread form) (NonNullEvenClifford.actionRotation value) :=
        by
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationSpreadAt_of_perpendicular value) vector
    nonNull perpendicular]
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpread
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation value)
    twoNonzero]

/-- Every non-null vector perpendicular to a cap anchor realizes the cap rotation spread when two is nonzero. -/
theorem TernaryForm.rotationSpreadAt_cap (form : Ternary.Basic.TernaryForm K)
    (anchor vector : Coordinates3.Vector K)
    (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0)
    (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector anchor)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) anchor defined) vector nonNull =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpread form)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) anchor defined) := by
  exact (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationSpreadAt_eq_rotationSpread
    ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) anchor defined))
    vector nonNull perpendicular twoNonzero

/-! ## Homogeneous and affine anchor products -/

/-- The total homogeneous anchor product. This is the even Clifford product under its geometric name; it remains defined
when an affine normalization is not. -/
def TernaryForm.homogeneousAnchorProduct (form : Ternary.Basic.TernaryForm K)
    (left right : form.EvenClifford) : form.EvenClifford :=
  EvenClifford.mul left right

/-- Scalar denominator for the affine product of two anchors. -/
def TernaryForm.anchorProductDenominator (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K) : K :=
  1 - form.determinant * form.bilinear left right

/-- Numerator vector for the affine product of two anchors. -/
def TernaryForm.anchorProductNumerator (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.sub (Coordinates3.Vector.add left right) (form.cliffordCross left right)

/-- The normalized form-relative anchor product. -/
def TernaryForm.anchorProduct (form : Ternary.Basic.TernaryForm K) (left right : Coordinates3.Vector K)
    (_defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ≠ 0) :
      Coordinates3.Vector K :=
  Coordinates3.Vector.scale ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹
    ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right)

/-- Multiplying scalar-one representatives gives the anchor-product denominator and numerator. -/
theorem TernaryForm.mul_capRepresentative (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K) :
    EvenClifford.mul ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) left)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) right) =
      ⟨(Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right,
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right⟩ := by
  apply EvenClifford.ext
  · unfold EvenClifford.mul EvenClifford.productScalar Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative
      Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator
    ring1
  · ext <;> unfold EvenClifford.mul EvenClifford.productVector
      Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative
        Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator Coordinates3.Vector.add
        Coordinates3.Vector.sub
      Coordinates3.Vector.scale <;> ring1

/-- The exact denominator identity for the affine anchor product. -/
theorem TernaryForm.cayleyDenominator_anchorProduct (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K)
    (productDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined) =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) left *
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) right /
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ^ 2 := by
  have denominatorCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right) productDefined
  have denominatorSquareCancel :
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ^ 2 *
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ ^ 2 = 1 := by
    calc
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ^ 2 *
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ ^ 2 =
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [denominatorCancel]; ring1
  have numeratorQuadrance := EvenClifford.quadrance_productVector form
    1 1 left right
  have productVectorEq :
      EvenClifford.productVector form 1 1 left right =
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right := by
    ext <;> unfold EvenClifford.productVector Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator
      Coordinates3.Vector.add Coordinates3.Vector.sub Coordinates3.Vector.scale <;> ring1
  rw [productVectorEq] at numeratorQuadrance
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator
    Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct
  rw [form.quadrance_scale]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [numeratorQuadrance]
  unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator
  change
      (1 - form.determinant * form.bilinear left right) ^ 2 *
        (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 = 1
    at denominatorSquareCancel
  calc
    1 + form.determinant *
        ((1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 *
          (1 ^ 2 * form.quadrance right +
            2 * 1 * 1 * form.bilinear left right +
            1 ^ 2 * form.quadrance left +
            form.determinant *
              (form.quadrance left * form.quadrance right -
                form.bilinear left right ^ 2))) =
      ((1 + form.determinant * form.quadrance left) *
          (1 + form.determinant * form.quadrance right)) *
        ((1 - form.determinant * form.bilinear left right)⁻¹ ^ 2) := by
      let remaining := form.determinant *
        (1 ^ 2 * form.quadrance right +
          2 * 1 * 1 * form.bilinear left right +
          1 ^ 2 * form.quadrance left +
          form.determinant *
            (form.quadrance left * form.quadrance right -
              form.bilinear left right ^ 2)) *
        (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2
      calc
        _ = 1 + remaining := by unfold remaining; ring1
        _ = ((1 - form.determinant * form.bilinear left right) ^ 2 *
              (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 +
            remaining) := by rw [denominatorSquareCancel]
        _ = _ := by unfold remaining; ring1
    _ = ((1 + form.determinant * form.quadrance left) *
          (1 + form.determinant * form.quadrance right)) *
        ((1 - form.determinant * form.bilinear left right) ^ 2)⁻¹ := by
      have inverseSquare := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {value : K} (valueNonzero : value
        ≠ 0) => (Purelib.Algebra.Field.Inverse.inverse_square (K := K) (value := value) valueNonzero : (value ^ 2)⁻¹ =
        value⁻¹ ^ 2))
        productDefined
      change
        ((1 - form.determinant * form.bilinear left right) ^ 2)⁻¹ =
          (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2
        at inverseSquare
      rw [inverseSquare]

/-- Defined input caps and a nonzero affine product denominator constructively certify the output cap denominator. -/
theorem TernaryForm.cayleyDenominator_anchorProduct_ne_zero (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K)
    (leftDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) left ≠ 0)
    (rightDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) right ≠ 0)
    (productDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined) ≠ 0 := by
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator_anchorProduct form) left right productDefined]
  exact Algebra.Field.ExplicitField.div_ne_zero
    (Algebra.Field.ExplicitField.mul_ne_zero leftDefined rightDefined)
    ((fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {value : K} (valueNonzero : value ≠ 0) =>
      (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero (K := K) (value := value) valueNonzero : value ^ 2
      ≠ 0)) productDefined)

/-- The product of scalar-one representatives is the normalized anchor representative scaled by the product denominator.
-/
theorem TernaryForm.capRepresentative_anchorProduct_scale (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K)
    (productDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ≠ 0) :
    EvenClifford.mul ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) left)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) right) =
      EvenClifford.scale ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form)
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined)) := by
  rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.mul_capRepresentative form)]
  apply EvenClifford.ext
  · unfold EvenClifford.scale Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative
    ring1
  · have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right) productDefined
    apply Coordinates3.Vector.ext
    · change ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).t =
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
          (((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).t)
      calc
        _ = 1 * ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).t := by
          rw [one_mul]
        _ = ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
              ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹) *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).t := by rw [cancel]
        _ = _ := by ring1
    · change ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).r =
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
          (((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).r)
      calc
        _ = 1 * ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).r := by
          rw [one_mul]
        _ = ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
              ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹) *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).r := by rw [cancel]
        _ = _ := by ring1
    · change ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).s =
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
          (((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).s)
      calc
        _ = 1 * ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).s := by
          rw [one_mul]
        _ = ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
              ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹) *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductNumerator form) left right).s := by rw [cancel]
        _ = _ := by ring1

/-- Form-relative Theorem 46: whenever all displayed affine denominators are nonzero, multiplication of caps is the cap
of the determinant-corrected anchor product. -/
theorem TernaryForm.capRotation_mul (form : Ternary.Basic.TernaryForm K)
    (left right : Coordinates3.Vector K)
    (leftDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) left ≠ 0)
    (rightDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) right ≠ 0)
    (productDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right ≠ 0) :
    SpecialOrthogonal.mul
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) left leftDefined)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) right rightDefined) =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator_anchorProduct_ne_zero form) left right
          leftDefined rightDefined productDefined) := by
  let outputDefined := (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator_anchorProduct_ne_zero form)
    left right leftDefined rightDefined productDefined
  have equivalent :
      (NonNullEvenClifford.Equivalent (NonNullEvenClifford.mul
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) left leftDefined)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) right rightDefined)))
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form)
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined)
            outputDefined) := by
    refine ⟨((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹,
      Algebra.Field.ExplicitField.inv_ne_zero productDefined, ?_⟩
    change (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined) =
      EvenClifford.scale ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹
        (EvenClifford.mul ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) left)
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) right))
    rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative_anchorProduct_scale form)]
    rw [EvenClifford.scale_scale]
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right) productDefined
    have reverseCancel :
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ *
          (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right = 1 := by
      calc
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ *
            (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right =
          (Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProductDenominator form) left right)⁻¹ := by ring1
        _ = 1 := cancel
    rw [reverseCancel, EvenClifford.one_scale]
  calc
    SpecialOrthogonal.mul
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) left leftDefined)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) right rightDefined) =
      (NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) left leftDefined)
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) right rightDefined))) :=
          (NonNullEvenClifford.actionRotation_mul _ _).symm
    _ = (NonNullEvenClifford.actionRotation ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined)
          outputDefined)) :=
      NonNullEvenClifford.actionRotation_respects_equivalent equivalent
    _ = (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.anchorProduct form) left right productDefined)
        outputDefined := rfl

/-! ## Affine normalization and the projective chart boundary -/

set_option genInjectivity false in
/-- Cached normalization of a non-null Clifford representative whose scalar coordinate is nonzero. -/
structure TernaryForm.CapNormalization (form : Ternary.Basic.TernaryForm K)
    (value : form.NonNullEvenClifford) where
  /-- The cached scalar-normalized affine anchor. -/ anchor : Coordinates3.Vector K
  /-- The cached anchor has nonzero cap denominator. -/ defined :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0
  /-- The cached cap representative is projectively equivalent to the original Clifford value. -/ equivalent :
    (NonNullEvenClifford.Equivalent ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) anchor defined))
    value

constructive_injectivity TernaryForm.CapNormalization

/-- Normalize a displayed Clifford representative into the affine cap chart. The scalar coordinate, anchor, denominator
certificate, and projective scale are all computed explicitly. -/
def TernaryForm.capNormalization (form : Ternary.Basic.TernaryForm K)
    (value : form.NonNullEvenClifford)
    (scalarNonzero : value.toEvenClifford.scalar ≠ 0) :
    Geometry.Rotations.Ternary.Cayley.TernaryForm.CapNormalization form value := by
  let anchor := Coordinates3.Vector.scale value.toEvenClifford.scalar⁻¹
    value.toEvenClifford.vector
  have scalarCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    value.toEvenClifford.scalar scalarNonzero
  have scaledRepresentative :
      value.toEvenClifford =
        Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.scale value.toEvenClifford.scalar
          ((Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) anchor) := by
    apply EvenClifford.ext
    · unfold Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.scale
        Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative
      ring1
    · apply Coordinates3.Vector.ext
      · change value.toEvenClifford.vector.t =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.t)
        calc
          _ = 1 * value.toEvenClifford.vector.t := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.t := by rw [scalarCancel]
          _ = _ := by ring1
      · change value.toEvenClifford.vector.r =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.r)
        calc
          _ = 1 * value.toEvenClifford.vector.r := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.r := by rw [scalarCancel]
          _ = _ := by ring1
      · change value.toEvenClifford.vector.s =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.s)
        calc
          _ = 1 * value.toEvenClifford.vector.s := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.s := by rw [scalarCancel]
          _ = _ := by ring1
  have defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor ≠ 0 := by
    intro denominatorZero
    apply value.normNonzero
    calc
      (EvenClifford.norm value.toEvenClifford) =
          (EvenClifford.norm (Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.scale
            value.toEvenClifford.scalar
            ((Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) anchor))) := by
              rw [← scaledRepresentative]
      _ = value.toEvenClifford.scalar ^ 2 *
          (EvenClifford.norm ((Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.capRepresentative form) anchor)) :=
        EvenClifford.norm_scale _ _
      _ = 0 := by
        rw [(Geometry.Rotations.Ternary.Cayley.TernaryForm.norm_capRepresentative form), denominatorZero, mul_zero]
  exact
    { anchor := anchor
      defined := defined
      equivalent :=
        ⟨value.toEvenClifford.scalar, scalarNonzero,
          scaledRepresentative⟩ }

/-- The normalized cap and its original Clifford representative define the same rotation. -/
theorem TernaryForm.CapNormalization.actionRotation_eq
    {form : Ternary.Basic.TernaryForm K} {value : form.NonNullEvenClifford}
    (normalization : Geometry.Rotations.Ternary.Cayley.TernaryForm.CapNormalization form value) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) normalization.anchor normalization.defined =
      (NonNullEvenClifford.actionRotation value) := by
  exact NonNullEvenClifford.actionRotation_respects_equivalent
    normalization.equivalent

/-- A scalar-zero non-null representative has a non-null vector coordinate. -/
theorem TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (scalarZero : value.toEvenClifford.scalar = 0) :
    form.quadrance value.toEvenClifford.vector ≠ 0 := by
  intro vectorNull
  apply value.normNonzero
  unfold EvenClifford.norm
  rw [scalarZero, vectorNull]
  ring1

/-- A non-null Clifford representative with scalar coordinate zero acts by the half turn around its vector coordinate.
-/
theorem TernaryForm.NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (scalarZero : value.toEvenClifford.scalar = 0) :
    (NonNullEvenClifford.actionRotation value) =
      form.halfTurnRotation value.toEvenClifford.vector
        ((Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero value)
          scalarZero) := by
  let nonNull := (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero
    value) scalarZero
  have valueEq :
      value = NonNullEvenClifford.halfTurnValue form
        value.toEvenClifford.vector nonNull := by
    apply NonNullEvenClifford.ext
    · exact scalarZero
    · rfl
  calc
    (NonNullEvenClifford.actionRotation value) =
        (NonNullEvenClifford.actionRotation (NonNullEvenClifford.halfTurnValue form
          value.toEvenClifford.vector nonNull)) :=
      congrArg NonNullEvenClifford.actionRotation valueEq
    _ = form.halfTurnRotation value.toEvenClifford.vector nonNull :=
      NonNullEvenClifford.halfTurnValue_actionRotation form
        value.toEvenClifford.vector nonNull

set_option genInjectivity false in
/-- The two constructive charts of a non-null Clifford representative. -/
inductive TernaryForm.CliffordChart (form : Ternary.Basic.TernaryForm K)
    (value : form.NonNullEvenClifford) where
  /-- A scalar-nonzero representative is retained through its certified affine normalization. -/ | affine (normalization
    : Geometry.Rotations.Ternary.Cayley.TernaryForm.CapNormalization form value)
  /-- A scalar-zero representative retains its non-null axis and equality with the corresponding half turn. -/ |
    atInfinity
      (scalarZero : value.toEvenClifford.scalar = 0)
      (axisNonNull : form.quadrance value.toEvenClifford.vector ≠ 0)
      (action_eq : (NonNullEvenClifford.actionRotation value) =
        form.halfTurnRotation value.toEvenClifford.vector axisNonNull)

constructive_injectivity TernaryForm.CliffordChart

/-- Execute the affine/half-turn chart decision once and cache all resulting denominators and representation
certificates. -/
def TernaryForm.cliffordChart [DecidableEq K] (form : Ternary.Basic.TernaryForm K)
    (value : form.NonNullEvenClifford) : Geometry.Rotations.Ternary.Cayley.TernaryForm.CliffordChart form value := by
  by_cases scalarZero : value.toEvenClifford.scalar = 0
  · exact Geometry.Rotations.Ternary.Cayley.TernaryForm.CliffordChart.atInfinity scalarZero
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero value)
        scalarZero)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
        value) scalarZero)
  · exact Geometry.Rotations.Ternary.Cayley.TernaryForm.CliffordChart.affine
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capNormalization form) value scalarZero)

/-- A half turn around a non-null axis has half spread one when two is nonzero. -/
theorem TernaryForm.rotationHalfSpread_halfTurn (form : Ternary.Basic.TernaryForm K)
    (axis : Coordinates3.Vector K) (nonNull : form.quadrance axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) (form.halfTurnRotation axis nonNull) = 1 :=
      by
  rw [← NonNullEvenClifford.halfTurnValue_actionRotation]
  rw [Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation _ twoNonzero]
  rw [NonNullEvenClifford.halfTurnValue_norm]
  have productNonzero := Algebra.Field.ExplicitField.mul_ne_zero
    form.determinantNonzero nonNull
  change form.determinant * form.quadrance axis /
      (form.determinant * form.quadrance axis) = 1
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  exact Algebra.Field.ExplicitField.mul_inv_cancel _ productNonzero

/-- A defined affine cap cannot have half spread one when two is nonzero. -/
theorem TernaryForm.rotationHalfSpread_cap_ne_one (form : Ternary.Basic.TernaryForm K)
    (anchor : Coordinates3.Vector K) (defined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form)
      anchor ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) anchor defined) ≠ 1 := by
  intro spreadOne
  have formula := (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_cap form) anchor defined twoNonzero
  rw [spreadOne] at formula
  have denominatorCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor) defined
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] at formula
  have weightedQuadranceEq :
      form.determinant * form.quadrance anchor =
        (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor := by
    calc
      form.determinant * form.quadrance anchor =
          form.determinant * form.quadrance anchor * 1 := by rw [mul_one]
      _ = form.determinant * form.quadrance anchor *
          ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor)⁻¹) := by rw
              [denominatorCancel]
      _ = (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor *
          (form.determinant * form.quadrance anchor *
            ((Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor)⁻¹) := by ring1
      _ = (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor * 1 := by rw [← formula]
      _ = (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor := by rw [mul_one]
  have impossible : (1 : K) = 0 := by
    calc
      (1 : K) = (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) anchor -
          form.determinant * form.quadrance anchor := by
        unfold Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator
        ring1
      _ = 0 := by rw [← weightedQuadranceEq]; ring1
  exact form.one_ne_zero impossible

/-- Form-relative cap injectivity. Projective faithfulness supplies a scale, and the two scalar coordinates equal to one
force that scale to be one. -/
theorem TernaryForm.capRotation_injective [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (left right : Coordinates3.Vector K)
    (leftDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) left ≠ 0)
    (rightDefined : (Geometry.Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form) right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) left leftDefined =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form) right rightDefined) :
    left = right := by
  have equivalent :=
    (NonNullEvenClifford.actionRotation_eq_iff_equivalent
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) left leftDefined)
      ((Geometry.Rotations.Ternary.Cayley.TernaryForm.capValue form) right rightDefined) twoNonzero).1 equal
  rcases equivalent with ⟨factor, factorNonzero, representativeEq⟩
  have scalarEq := congrArg EvenClifford.scalar representativeEq
  have factorOne : factor = 1 := by
    change (1 : K) = factor * 1 at scalarEq
    simpa only [mul_one] using scalarEq.symm
  have vectorEq := congrArg EvenClifford.vector representativeEq
  change right = Coordinates3.Vector.scale factor left at vectorEq
  rw [factorOne, Coordinates3.Vector.one_scale] at vectorEq
  exact vectorEq.symm

/-! ## A cached canonical axis and spread witness for every rotation -/

set_option genInjectivity false in
/-- Cached representative, chart, factorization, axis, and geometric spread data for an arbitrary displayed form
rotation. The first half-turn axis from the constructive factorization is automatically a non-null perpendicular test
direction for the product representative's vector coordinate. -/
structure TernaryForm.RotationAxisSpreadWitness (form : Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  /-- The cached two-half-turn factorization of the input rotation. -/ factorization :
    TernaryForm.TwoHalfTurnFactorization form rotation
  /-- The cached non-null Clifford representative. -/ representative : form.NonNullEvenClifford
  /-- The representative is exactly the preimage computed from the cached factorization. -/ representative_eq :
    representative = (TwoHalfTurnFactorization.cliffordPreimage factorization)
  /-- The cached Clifford representative acts as the original rotation. -/ represents :
    (NonNullEvenClifford.actionRotation representative) = rotation
  /-- The retained axis vector. -/ axis : Coordinates3.Vector K
  /-- The axis is the vector coordinate of the cached Clifford representative. -/ axis_eq : axis =
    representative.toEvenClifford.vector
  /-- The retained direction used to measure the geometric spread. -/ perpendicular : Coordinates3.Vector K
  /-- The retained test direction has nonzero form quadrance. -/ perpendicularNonNull : form.quadrance perpendicular ≠ 0
  /-- The retained test direction is perpendicular to the cached axis. -/ perpendicularToAxis : form.Perpendicular
    perpendicular axis
  /-- The retained affine normalization or half-turn boundary classification. -/ chart :
    Geometry.Rotations.Ternary.Cayley.TernaryForm.CliffordChart form representative
  /-- The rotation half spread equals the determinant-weighted cached axis quadrance divided by the representative norm.
  -/ halfSpread_eq :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation =
      form.determinant * form.quadrance axis /
        (EvenClifford.norm representative.toEvenClifford)
  /-- The retained perpendicular test direction realizes the rotation spread. -/ spread_eq :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt form) rotation perpendicular perpendicularNonNull =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpread form) rotation

constructive_injectivity TernaryForm.RotationAxisSpreadWitness

/-- The cached two-half-turn data are simultaneously the paper's two-reflection factorization: negating both reflection
matrices leaves their product unchanged. -/
theorem TernaryForm.TwoHalfTurnFactorization.reflectionProductMatrix
    {form : Ternary.Basic.TernaryForm K} {rotation : form.SpecialOrthogonal}
    (factorization : TernaryForm.TwoHalfTurnFactorization form rotation) :
    Matrix3.mul
        (form.reflection factorization.firstAxis factorization.firstNonNull)
        (form.reflection factorization.secondAxis factorization.secondNonNull) =
      rotation.matrix := by
  have rotationMatrix := congrArg
    (fun value : form.SpecialOrthogonal => value.matrix)
    factorization.rotation_eq
  change Matrix3.mul
      (form.halfTurn factorization.firstAxis factorization.firstNonNull)
      (form.halfTurn factorization.secondAxis factorization.secondNonNull) =
    rotation.matrix at rotationMatrix
  unfold TernaryForm.halfTurn at rotationMatrix
  rw [Matrix3.mul_neg_neg] at rotationMatrix
  exact rotationMatrix

/-- Construct the uniform form-relative axis/spread interface from the same cached two-half-turn data used by the
projective Clifford correspondence. -/
def TernaryForm.rotationAxisSpreadWitness [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness form rotation := by
  let factorization := form.twoHalfTurnFactorization rotation twoNonzero
  let representative := (TwoHalfTurnFactorization.cliffordPreimage factorization)
  have represents : (NonNullEvenClifford.actionRotation representative) = rotation :=
    (TwoHalfTurnFactorization.cliffordPreimage_actionRotation factorization)
  have perpendicularToAxis :
      form.Perpendicular factorization.firstAxis
        representative.toEvenClifford.vector :=

      (TernaryForm.TwoHalfTurnFactorization.firstAxis_perpendicular_cliffordPreimage
      factorization)
  have halfSpreadFormula :=
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation representative)
      twoNonzero
  have spreadFormula :=
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationSpreadAt_eq_rotationSpread
      representative)
      factorization.firstAxis factorization.firstNonNull
      perpendicularToAxis twoNonzero
  rw [represents] at halfSpreadFormula spreadFormula
  exact
    { factorization := factorization
      representative := representative
      representative_eq := rfl
      represents := represents
      axis := representative.toEvenClifford.vector
      axis_eq := rfl
      perpendicular := factorization.firstAxis
      perpendicularNonNull := factorization.firstNonNull
      perpendicularToAxis := perpendicularToAxis
      chart := (Geometry.Rotations.Ternary.Cayley.TernaryForm.cliffordChart form) representative
      halfSpread_eq := halfSpreadFormula
      spread_eq := spreadFormula }

/-- Uniform geometric-spread theorem for any other non-null direction perpendicular to the cached canonical axis. -/
theorem TernaryForm.RotationAxisSpreadWitness.spread_independent
    {form : Ternary.Basic.TernaryForm K} {rotation : form.SpecialOrthogonal}
    (witness : Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness form rotation)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector witness.axis)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpreadAt form) rotation vector nonNull =
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationSpread form) rotation := by
  have representativePerpendicular :
      form.Perpendicular vector witness.representative.toEvenClifford.vector := by
    rw [← witness.axis_eq]
    exact perpendicular
  have formula :=
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.rotationSpreadAt_eq_rotationSpread
      witness.representative)
      vector nonNull representativePerpendicular twoNonzero
  rw [witness.represents] at formula
  exact formula

/-- Any rotation whose half spread is not one is recovered as the cap of an explicit normalized anchor computed from its
cached representative. -/
def TernaryForm.RotationAxisSpreadWitness.capNormalizationOfHalfSpreadNeOne
    [DecidableEq K] {form : Ternary.Basic.TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (witness : Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation ≠ 1) :
    Geometry.Rotations.Ternary.Cayley.TernaryForm.CapNormalization form witness.representative := by
  have scalarNonzero :
      witness.representative.toEvenClifford.scalar ≠ 0 := by
    intro scalarZero
    apply notHalfTurn
    have vectorNonNull :=
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero
        witness.representative) scalarZero
    calc
      (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation =
          (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) (NonNullEvenClifford.actionRotation
            witness.representative) := by
        rw [witness.represents]
      _ = (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form)
          (form.halfTurnRotation
            witness.representative.toEvenClifford.vector vectorNonNull) := by
        rw
          [(NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
          witness.representative)
          scalarZero]
      _ = 1 := (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_halfTurn form) _ vectorNonNull
        twoNonzero
  exact (Geometry.Rotations.Ternary.Cayley.TernaryForm.capNormalization form) witness.representative scalarNonzero

/-- Normalizing the cached representative recovers the original rotation whenever its half spread differs from one. -/
theorem TernaryForm.RotationAxisSpreadWitness.cap_recovery
    [DecidableEq K] {form : Ternary.Basic.TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (witness : Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : (Geometry.Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread form) rotation ≠ 1) :
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form)
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).anchor
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).defined = rotation := by
  calc
    (Geometry.Rotations.Ternary.Cayley.TernaryForm.capRotation form)
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).anchor
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).defined =
      (NonNullEvenClifford.actionRotation witness.representative) :=
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).actionRotation_eq
    _ = rotation := witness.represents

end TernaryForm

end Purelib.Geometry.Rotations.Ternary.Cayley
