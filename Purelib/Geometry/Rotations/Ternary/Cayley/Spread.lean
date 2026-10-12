module

public import Purelib.Geometry.Rotations.Ternary.Cayley
public import Purelib.Geometry.Quadratic.Ternary.Spread
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Geometry.Rotations.Ternary.Reflection
import Purelib.Geometry.Rotations.Ternary.Characteristic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

/-!
# Geometric spreads of ternary rotations

The trace spread polynomial agrees with the original form's vector spread
on every non-null direction perpendicular to a cap or half-turn axis.
The certified perpendicular-vector construction provides a retained
measurement direction whenever the axis is non-null.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Characteristic.Nonzero
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Inverting a displayed ternary rotation preserves its original trace half spread. -/
theorem rotationHalfSpread_inverse (form : Form K) (rotation : form.SpecialOrthogonal) :
    rotationHalfSpread form (Basic.TernaryForm.SpecialOrthogonal.inverse rotation) =
      rotationHalfSpread form rotation := by
  unfold rotationHalfSpread
  change (3 - Matrix3.trace rotation.inverseMatrix) / 4 = (3 - Matrix3.trace rotation.matrix) / 4
  rw [rotation.trace_inverseMatrix]

/-- The half spread of a squared rotation is the original rotation's canonical spread.

The finite Newton identity gives the squared trace. Equality of trace and
principal trace for a ternary rotation then yields `4p(1-p)`, with the
supplied nonzero-two certificate justifying division by four.
-/
theorem rotationHalfSpread_square (form : Form K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationHalfSpread form (Basic.TernaryForm.SpecialOrthogonal.mul rotation rotation) =
      rotationSpread form rotation := by
  have fourNonzero := four_ne_zero twoNonzero
  unfold rotationSpread rotationHalfSpread
  change (3 - Matrix3.trace (Matrix3.mul rotation.matrix rotation.matrix)) / 4 =
    4 * ((3 - Matrix3.trace rotation.matrix) / 4) * (1 - (3 - Matrix3.trace rotation.matrix) / 4)
  rw [Matrix3.trace_square, rotation.principalTrace_matrix]
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    _ = 3 - (Matrix3.trace rotation.matrix ^ 2 - 2 * Matrix3.trace rotation.matrix) :=
      ExplicitField.div_mul_cancel _ fourNonzero
    _ = (3 - Matrix3.trace rotation.matrix) * (4 - (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = ((3 - Matrix3.trace rotation.matrix) / 4 * 4) *
        (4 - (3 - Matrix3.trace rotation.matrix) / 4 * 4) := by
      rw [ExplicitField.div_mul_cancel _ fourNonzero]
    _ = _ := by ring1

/-- The half spread of two half turns equals the spread of their non-null axes.

The two negative reflection matrices have the same product as the original
reflections. Their trace formula gives the spread of the retained normals,
and nonzero two permits division by four.
-/
theorem rotationHalfSpread_halfTurn_mul (form : Form K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationHalfSpread form (Basic.TernaryForm.SpecialOrthogonal.mul
        (form.halfTurnRotation first firstNonNull) (form.halfTurnRotation second secondNonNull)) =
      form.spread first second firstNonNull secondNonNull := by
  unfold rotationHalfSpread
  change (3 - Matrix3.trace (Matrix3.mul (form.halfTurn first firstNonNull)
    (form.halfTurn second secondNonNull))) / 4 = _
  unfold Form.halfTurn
  rw [Matrix3.mul_neg_neg, form.trace_reflection_product]
  apply ExplicitField.eq_of_mul_eq_mul_right (four_ne_zero twoNonzero)
  rw [ExplicitField.div_mul_cancel _ (four_ne_zero twoNonzero)]
  ring1

/-- The half spread of two reflections equals the spread of their non-null normals.

The determinant-one isometry retains the original row-order reflection
product. Equality with the two half turns gives the same normal-spread law.
-/
theorem rotationHalfSpread_reflectionProduct (form : Form K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationHalfSpread form (form.reflectionProductRotation first second firstNonNull secondNonNull) =
      form.spread first second firstNonNull secondNonNull := by
  rw [← form.halfTurnRotation_mul]
  exact rotationHalfSpread_halfTurn_mul form first second firstNonNull secondNonNull twoNonzero

/-- The normalized pairing measurement equals the vector spread in the original preserved form.

Quadrance preservation identifies the two denominators. Non-nullity
justifies squaring the inverse of the original vector quadrance.
-/
theorem rotationSpreadAt_eq_spread (form : Form K) (rotation : form.SpecialOrthogonal)
    (vector : Vector3 K) (nonNull : form.quadrance vector ≠ 0) :
    rotationSpreadAt form rotation vector nonNull =
      form.spread vector (Form.Isometry.act rotation.toIsometry vector) nonNull
        (rotation.toIsometry.quadrance_act_ne_zero vector nonNull) := by
  unfold rotationSpreadAt Form.spread
  rw [rotation.quadrance_act vector, ← pow_two]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [Inverse.inverse_square nonNull]
  ring1

/-- Every non-null direction perpendicular to a cap axis measures its canonical rotation spread.

The shared Clifford measurement law supplies the trace polynomial. The
form-spread equality makes that law a statement about the two actual vectors.
-/
theorem spread_cap (form : Form K) (axis vector : Vector3 K)
    (defined : cayleyDenominator form axis ≠ 0) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector axis) (twoNonzero : (2 : K) ≠ 0) :
    form.spread vector (Form.Isometry.act (capRotation form axis defined).toIsometry vector) nonNull
        ((capRotation form axis defined).toIsometry.quadrance_act_ne_zero vector nonNull) =
      rotationSpread form (capRotation form axis defined) := by
  rw [← rotationSpreadAt_eq_spread]
  exact rotationSpreadAt_cap form axis vector defined nonNull perpendicular twoNonzero

/-- Every non-null direction perpendicular to a half-turn axis measures zero spread.

The half turn negates the measurement vector. Its normalized pairing with
that image is minus one, so the geometric spread vanishes.
-/
theorem spread_halfTurn (form : Form K) (axis vector : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector axis) :
    form.spread vector (Form.Isometry.act (form.halfTurnRotation axis axisNonNull).toIsometry vector) nonNull
        ((form.halfTurnRotation axis axisNonNull).toIsometry.quadrance_act_ne_zero vector nonNull) = 0 := by
  rw [← rotationSpreadAt_eq_spread]
  unfold rotationSpreadAt
  change 1 - (form.bilinear vector (Matrix3.rowMul vector (form.halfTurn axis axisNonNull)) /
    form.quadrance vector) ^ 2 = 0
  rw [form.rowMul_halfTurn_of_perpendicular axis axisNonNull vector perpendicular, form.bilinear_neg_right]
  change 1 - (-form.quadrance vector / form.quadrance vector) ^ 2 = 0
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    _ = 1 - (-(form.quadrance vector * (form.quadrance vector)⁻¹)) ^ 2 := by ring1
    _ = 0 := by rw [ExplicitField.mul_inv_cancel _ nonNull]; ring1

/-- The perpendicular half-turn measurement equals its canonical trace spread polynomial. -/
theorem spread_halfTurn_eq_rotationSpread (form : Form K) (axis vector : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector axis) (twoNonzero : (2 : K) ≠ 0) :
    form.spread vector (Form.Isometry.act (form.halfTurnRotation axis axisNonNull).toIsometry vector) nonNull
        ((form.halfTurnRotation axis axisNonNull).toIsometry.quadrance_act_ne_zero vector nonNull) =
      rotationSpread form (form.halfTurnRotation axis axisNonNull) := by
  rw [spread_halfTurn form axis vector axisNonNull nonNull perpendicular]
  unfold rotationSpread
  rw [rotationHalfSpread_halfTurn form axis axisNonNull twoNonzero]
  ring1

/-- Construct a retained non-null perpendicular direction that realizes a cap's geometric spread.

The result keeps the original form-indexed perpendicular witness and its
non-nullity certificate. The measurement uses that exact retained vector.
-/
@[expose] def capSpreadWitness [DecidableEq K] (form : Form K) (axis : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (defined : cayleyDenominator form axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' witness : form.PerpendicularNonNullVectorWitness axis,
      form.spread witness.value (Form.Isometry.act (capRotation form axis defined).toIsometry witness.value)
        witness.nonNull
        ((capRotation form axis defined).toIsometry.quadrance_act_ne_zero witness.value witness.nonNull) =
          rotationSpread form (capRotation form axis defined) := by
  let witness := form.perpendicularNonNullVectorWitness axis axisNonNull twoNonzero
  exact ⟨witness, spread_cap form axis witness.value defined witness.nonNull witness.perpendicular twoNonzero⟩

/-- Construct a retained non-null perpendicular direction that realizes a half turn's geometric spread.

The original perpendicular-vector constructor supplies the measurement
direction and both domain certificates for the geometric spread law.
-/
@[expose] def halfTurnSpreadWitness [DecidableEq K] (form : Form K) (axis : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Σ' witness : form.PerpendicularNonNullVectorWitness axis,
      form.spread witness.value (Form.Isometry.act (form.halfTurnRotation axis axisNonNull).toIsometry witness.value)
        witness.nonNull
        ((form.halfTurnRotation axis axisNonNull).toIsometry.quadrance_act_ne_zero witness.value witness.nonNull) =
          rotationSpread form (form.halfTurnRotation axis axisNonNull) := by
  let witness := form.perpendicularNonNullVectorWitness axis axisNonNull twoNonzero
  exact ⟨witness, spread_halfTurn_eq_rotationSpread form axis witness.value axisNonNull
    witness.nonNull witness.perpendicular twoNonzero⟩

namespace RotationAxisSpreadWitness

/-- Any non-null direction perpendicular to the cached axis measures the original rotation's geometric spread. -/
theorem geometric_spread_independent {form : Form K} {rotation : form.SpecialOrthogonal}
    (witness : RotationAxisSpreadWitness form rotation) (vector : Vector3 K)
    (nonNull : form.quadrance vector ≠ 0) (perpendicular : form.Perpendicular vector witness.axis)
    (twoNonzero : (2 : K) ≠ 0) :
    form.spread vector (Form.Isometry.act rotation.toIsometry vector) nonNull
        (rotation.toIsometry.quadrance_act_ne_zero vector nonNull) = rotationSpread form rotation := by
  rw [← rotationSpreadAt_eq_spread]
  exact witness.spread_independent vector nonNull perpendicular twoNonzero

end RotationAxisSpreadWitness

/-- Construct a cached axis witness whose retained perpendicular vector measures the original rotation's spread.

The factorization, Clifford representative, axis and measurement vector are
computed once by the original axis/spread builder. The returned equality
relates that same measurement to the trace spread polynomial.
-/
@[expose] def geometricSpreadWitness [DecidableEq K] (form : Form K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' witness : RotationAxisSpreadWitness form rotation,
      form.spread witness.perpendicular (Form.Isometry.act rotation.toIsometry witness.perpendicular)
        witness.perpendicularNonNull
        (rotation.toIsometry.quadrance_act_ne_zero witness.perpendicular witness.perpendicularNonNull) =
          rotationSpread form rotation := by
  let witness := rotationAxisSpreadWitness form rotation twoNonzero
  exact ⟨witness, witness.geometric_spread_independent witness.perpendicular witness.perpendicularNonNull
    witness.perpendicularToAxis twoNonzero⟩

end Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm

end
