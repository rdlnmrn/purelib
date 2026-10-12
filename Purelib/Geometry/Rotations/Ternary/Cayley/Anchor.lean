module

public import Purelib.Geometry.Rotations.Ternary.Cayley.Matrix
import Purelib.Geometry.Rotations.Ternary.Characteristic
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Anchors of displayed ternary rotations

An anchor is computed from the original matrix, its retained inverse and
one scalar inverse. The finite adjugate identity identifies this result
with the Cayley inverse formula, on exactly the non-half-turn domain.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Characteristic.Nonzero
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] {form : TernaryForm K}

/-- The anchor denominator is one plus the trace of the original rotation matrix. -/
@[expose] def anchorDenominator (rotation : form.SpecialOrthogonal) : K :=
  1 + Matrix3.trace rotation.matrix

/-- The determinant of identity plus a rotation is twice its anchor denominator.

The reciprocal characteristic polynomial at minus one computes this
determinant. The claim requires no division or characteristic restriction.
-/
theorem determinant_identity_add (rotation : form.SpecialOrthogonal) :
    Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) =
      2 * rotation.anchorDenominator := by
  have negative : Matrix3.sub (Matrix3.scale (-1 : K) Matrix3.identity) rotation.matrix =
      Matrix3.neg (Matrix3.add Matrix3.identity rotation.matrix) := by
    ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.identity Matrix3.neg Matrix3.add <;> ring1
  have characteristic := rotation.characteristicValue_matrix (-1)
  unfold Matrix3.characteristicValue at characteristic
  rw [negative, Matrix3.determinant_neg] at characteristic
  unfold anchorDenominator
  calc
    _ = -(-Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix)) := (neg_neg _).symm
    _ = -((-1 - 1) * ((-1) ^ 2 - (Matrix3.trace rotation.matrix - 1) * (-1) + 1)) :=
      congrArg Neg.neg characteristic
    _ = _ := by ring1

/-- Multiplying half spread by four gives three minus the original matrix trace. -/
theorem four_mul_halfSpread (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    4 * Cayley.TernaryForm.rotationHalfSpread form rotation = 3 - Matrix3.trace rotation.matrix := by
  unfold Cayley.TernaryForm.rotationHalfSpread
  rw [mul_comm]
  exact ExplicitField.div_mul_cancel _ (four_ne_zero twoNonzero)

/-- The anchor denominator is four times the complement of the original half spread. -/
theorem anchorDenominator_eq (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    rotation.anchorDenominator = 4 * (1 - Cayley.TernaryForm.rotationHalfSpread form rotation) := by
  unfold anchorDenominator
  calc
    _ = 4 * (1 - Cayley.TernaryForm.rotationHalfSpread form rotation) +
        (4 * Cayley.TernaryForm.rotationHalfSpread form rotation - (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = _ := by rw [rotation.four_mul_halfSpread twoNonzero]; ring1

/-- The anchor denominator is nonzero exactly when half spread differs from one. -/
theorem anchorDenominator_ne_zero_iff (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    rotation.anchorDenominator ≠ 0 ↔ Cayley.TernaryForm.rotationHalfSpread form rotation ≠ 1 := by
  constructor
  · intro defined halfSpreadOne
    apply defined
    rw [rotation.anchorDenominator_eq twoNonzero, halfSpreadOne]
    ring1
  · intro notHalfTurn denominatorZero
    apply notHalfTurn
    have complementZero : 1 - Cayley.TernaryForm.rotationHalfSpread form rotation = 0 :=
      ExplicitField.eq_zero_of_mul_eq_zero_left (four_ne_zero twoNonzero)
        ((rotation.anchorDenominator_eq twoNonzero).symm.trans denominatorZero)
    calc
      _ = 1 - (1 - Cayley.TernaryForm.rotationHalfSpread form rotation) := by ring1
      _ = 1 := by rw [complementZero]; ring1

/-- Identity plus a rotation is invertible exactly when its half spread differs from one. -/
theorem determinant_identity_add_ne_zero_iff (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔
      Cayley.TernaryForm.rotationHalfSpread form rotation ≠ 1 := by
  constructor
  · intro determinantNonzero
    apply (rotation.anchorDenominator_ne_zero_iff twoNonzero).mp
    intro denominatorZero
    apply determinantNonzero
    rw [rotation.determinant_identity_add, denominatorZero, mul_zero]
  · intro notHalfTurn
    rw [rotation.determinant_identity_add]
    exact ExplicitField.mul_ne_zero twoNonzero
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)

/-- Compute the anchor from the original matrix and retained inverse with one scalar inverse.

The supplied nonzero denominator is the domain certificate. The operation
reuses the exact inverse already stored by the rotation and performs no
new matrix inversion.
-/
@[expose] def anchor (rotation : form.SpecialOrthogonal) (_defined : rotation.anchorDenominator ≠ 0) : Matrix3 K :=
  Matrix3.scale rotation.anchorDenominator⁻¹ (Matrix3.sub rotation.matrix rotation.inverseMatrix)

/-- The difference between a rotation and its inverse satisfies the Cayley numerator identity.

The retained inverse is the original matrix adjugate. Its finite quadratic
expansion and equality of trace and principal trace give the product law
without a characteristic restriction or a selected axis.
-/
theorem sub_inverse_mul_identity_add (rotation : form.SpecialOrthogonal) :
    Matrix3.mul (Matrix3.sub rotation.matrix rotation.inverseMatrix)
        (Matrix3.add Matrix3.identity rotation.matrix) =
      Matrix3.scale rotation.anchorDenominator (Matrix3.sub rotation.matrix Matrix3.identity) := by
  rw [Matrix3.mul_sub_left, Matrix3.mul_add_right, Matrix3.mul_add_right,
    Matrix3.mul_identity, Matrix3.mul_identity, rotation.inverse_mul_matrix,
    ← rotation.adjugate_matrix, Matrix3.adjugate_expansion, rotation.principalTrace_matrix]
  ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale anchorDenominator <;> ring1

/-- The computed anchor times identity plus the rotation equals rotation minus identity. -/
theorem anchor_mul_identity_add (rotation : form.SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0) :
    Matrix3.mul (rotation.anchor defined) (Matrix3.add Matrix3.identity rotation.matrix) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  unfold anchor
  rw [Matrix3.mul_scale_left, rotation.sub_inverse_mul_identity_add, Matrix3.scale_scale,
    mul_comm, ExplicitField.mul_inv_cancel _ defined, Matrix3.one_scale]

/-- Identity plus a rotation times its computed anchor gives rotation minus identity. -/
theorem identity_add_mul_anchor (rotation : form.SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0) :
    Matrix3.mul (Matrix3.add Matrix3.identity rotation.matrix) (rotation.anchor defined) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  have numerator : Matrix3.mul (Matrix3.add Matrix3.identity rotation.matrix)
        (Matrix3.sub rotation.matrix rotation.inverseMatrix) =
      Matrix3.scale rotation.anchorDenominator (Matrix3.sub rotation.matrix Matrix3.identity) := by
    rw [Matrix3.mul_add_left, Matrix3.mul_sub_right, Matrix3.mul_sub_right,
      Matrix3.identity_mul, Matrix3.identity_mul, rotation.matrix_mul_inverse,
      ← rotation.adjugate_matrix, Matrix3.adjugate_expansion, rotation.principalTrace_matrix]
    ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale anchorDenominator <;> ring1
  unfold anchor
  rw [Matrix3.mul_scale_right, numerator, Matrix3.scale_scale,
    mul_comm, ExplicitField.mul_inv_cancel _ defined, Matrix3.one_scale]

/-- The computed anchor equals the literal Cayley inverse matrix formula.

The caller supplies the matching invertibility certificate for identity
plus the original rotation. Multiplication by that exact inverse transports
the numerator identity to the paper's formula.
-/
theorem anchor_eq_inverseFormula (rotation : form.SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0)
    (determinantNonzero : Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0) :
    rotation.anchor defined = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
      (Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix) determinantNonzero) := by
  calc
    _ = Matrix3.mul (rotation.anchor defined) Matrix3.identity := (Matrix3.mul_identity _).symm
    _ = Matrix3.mul (rotation.anchor defined)
        (Matrix3.mul (Matrix3.add Matrix3.identity rotation.matrix)
          (Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix) determinantNonzero)) := by
      rw [Matrix3.mul_inverse]
    _ = _ := by rw [← Matrix3.mul_assoc, rotation.anchor_mul_identity_add]

/-- Multiplying a rotation's anchor by its original form matrix gives an antisymmetric matrix.

The retained inverse converts the second term to the form times the
transposed rotation. Symmetry of the form interchanges these two terms
under transposition.
-/
theorem anchor_mul_form_antisymmetric (rotation : form.SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) :
    Matrix3.transpose (Matrix3.mul (rotation.anchor defined) form.matrix) =
      Matrix3.neg (Matrix3.mul (rotation.anchor defined) form.matrix) := by
  have inverseGram : Matrix3.mul rotation.inverseMatrix form.matrix =
      Matrix3.mul form.matrix (Matrix3.transpose rotation.matrix) := by
    rw [rotation.inverseMatrix_eq_transpose_conjugate, Matrix3.mul_assoc,
      form.inverse_mul_matrix, Matrix3.mul_identity]
  have normalized : Matrix3.mul (rotation.anchor defined) form.matrix =
      Matrix3.scale rotation.anchorDenominator⁻¹
        (Matrix3.sub (Matrix3.mul rotation.matrix form.matrix)
          (Matrix3.mul form.matrix (Matrix3.transpose rotation.matrix))) := by
    unfold anchor
    rw [Matrix3.mul_scale_left, Matrix3.mul_sub_left, inverseGram]
  rw [normalized, Matrix3.transpose_scale, Matrix3.transpose_sub,
    Matrix3.transpose_mul, Matrix3.transpose_mul, form.symmetric, Matrix3.transpose_transpose]
  ext <;> unfold Matrix3.scale Matrix3.sub Matrix3.neg <;> ring1

/-- The adjoint-antisymmetric part of a rotation is half its difference from the retained inverse. -/
@[expose] def antisymmetricPart (rotation : form.SpecialOrthogonal) (_twoNonzero : (2 : K) ≠ 0) : Matrix3 K :=
  Matrix3.scale (2 : K)⁻¹ (Matrix3.sub rotation.matrix rotation.inverseMatrix)

/-- The anchor is the adjoint-antisymmetric part scaled by two over one plus trace. -/
theorem anchor_eq_antisymmetricPart (rotation : form.SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    rotation.anchor defined = Matrix3.scale (2 / rotation.anchorDenominator)
      (rotation.antisymmetricPart twoNonzero) := by
  unfold anchor antisymmetricPart
  rw [Matrix3.scale_scale, ExplicitField.div_eq_mul_inv]
  have coefficient : rotation.anchorDenominator⁻¹ = 2 * rotation.anchorDenominator⁻¹ * (2 : K)⁻¹ := by
    calc
      _ = (2 * (2 : K)⁻¹) * rotation.anchorDenominator⁻¹ := by
        rw [ExplicitField.mul_inv_cancel _ twoNonzero, one_mul]
      _ = _ := by ring1
  exact congrArg (fun scalar => Matrix3.scale scalar (Matrix3.sub rotation.matrix rotation.inverseMatrix)) coefficient

/-- Inverting a ternary rotation preserves the computed anchor denominator. -/
theorem anchorDenominator_inverse (rotation : form.SpecialOrthogonal) :
    (Basic.TernaryForm.SpecialOrthogonal.inverse rotation).anchorDenominator = rotation.anchorDenominator := by
  unfold anchorDenominator
  change 1 + Matrix3.trace rotation.inverseMatrix = 1 + Matrix3.trace rotation.matrix
  rw [rotation.trace_inverseMatrix]

/-- Inverting a ternary rotation negates its original computed anchor.

The retained inverse exchanges the original matrix and inverse matrix.
Their trace denominator is unchanged, so their antisymmetric difference
and its normalized anchor change sign.
-/
theorem anchor_inverse (rotation : form.SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0) :
    (Basic.TernaryForm.SpecialOrthogonal.inverse rotation).anchor
        (by rw [rotation.anchorDenominator_inverse]; exact defined) = Matrix3.neg (rotation.anchor defined) := by
  change Matrix3.scale (Basic.TernaryForm.SpecialOrthogonal.inverse rotation).anchorDenominator⁻¹
    (Matrix3.sub rotation.inverseMatrix rotation.matrix) = _
  rw [rotation.anchorDenominator_inverse]
  unfold anchor
  ext <;> unfold Matrix3.scale Matrix3.sub Matrix3.neg <;> ring1

/-- Recover the original skew matrix from a defined form-relative cap.

The cap resolvent identity gives the same numerator equation as the
computed rotation anchor. The retained inverse of identity plus the cap
cancels that equation, preserving the original cap and axis owners.
-/
theorem anchor_capRotation (axis : Vector3 K) (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (Cayley.TernaryForm.capRotation form axis defined).anchor
        ((Cayley.TernaryForm.capRotation form axis defined).anchorDenominator_ne_zero_iff twoNonzero |>.mpr
          (Cayley.TernaryForm.rotationHalfSpread_cap_ne_one form axis defined twoNonzero)) =
      form.actionSkew axis := by
  let rotation := Cayley.TernaryForm.capRotation form axis defined
  let anchorDefined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr
    (Cayley.TernaryForm.rotationHalfSpread_cap_ne_one form axis defined twoNonzero)
  let determinantNonzero := (rotation.determinant_identity_add_ne_zero_iff twoNonzero).mpr
    (Cayley.TernaryForm.rotationHalfSpread_cap_ne_one form axis defined twoNonzero)
  let sumInverse := Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix) determinantNonzero
  have skewNumerator : Matrix3.mul (Matrix3.add Matrix3.identity rotation.matrix) (form.actionSkew axis) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
    rw [Matrix3.mul_add_left, Matrix3.identity_mul]
    calc
      _ = Matrix3.add
          (Matrix3.sub rotation.matrix
            (Matrix3.mul rotation.matrix (Matrix3.sub Matrix3.identity (form.actionSkew axis))))
          (form.actionSkew axis) := by
        rw [Matrix3.mul_sub_right, Matrix3.mul_identity]
        ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
      _ = _ := by
        rw [form.capRotation_matrix_mul_resolvent]
        ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
  change rotation.anchor anchorDefined = _
  calc
    _ = Matrix3.mul Matrix3.identity (rotation.anchor anchorDefined) := (Matrix3.identity_mul _).symm
    _ = Matrix3.mul (Matrix3.mul sumInverse (Matrix3.add Matrix3.identity rotation.matrix))
        (rotation.anchor anchorDefined) := by rw [Matrix3.inverse_mul]
    _ = Matrix3.mul sumInverse (Matrix3.sub rotation.matrix Matrix3.identity) := by
      rw [Matrix3.mul_assoc, rotation.identity_add_mul_anchor]
    _ = Matrix3.mul sumInverse
        (Matrix3.mul (Matrix3.add Matrix3.identity rotation.matrix) (form.actionSkew axis)) := by
      rw [skewNumerator]
    _ = form.actionSkew axis := by rw [← Matrix3.mul_assoc, Matrix3.inverse_mul, Matrix3.identity_mul]

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford (actionRotation actionMatrix)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Characteristic.Nonzero
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] {form : Form K}

/-- The anchor denominator of a Clifford rotation is four times its squared scalar over its norm.

The trace formula and the original nonzero norm give the equality. No
normalization or selection of a representative is needed.
-/
theorem anchorDenominator_actionRotation (value : form.NonNullEvenClifford) :
    (actionRotation value).anchorDenominator =
      4 * value.toEvenClifford.scalar ^ 2 / EvenClifford.norm value.toEvenClifford := by
  unfold Form.SpecialOrthogonal.anchorDenominator
  change 1 + Matrix3.trace (actionMatrix value) = _
  rw [Cayley.TernaryForm.NonNullEvenClifford.trace_actionMatrix]
  calc
    _ = EvenClifford.norm value.toEvenClifford * (EvenClifford.norm value.toEvenClifford)⁻¹ +
        (EvenClifford.norm value.toEvenClifford)⁻¹ *
          (3 * value.toEvenClifford.scalar ^ 2 - form.determinant * form.quadrance value.toEvenClifford.vector) := by
      rw [ExplicitField.mul_inv_cancel _ value.normNonzero]
    _ = 4 * value.toEvenClifford.scalar ^ 2 * (EvenClifford.norm value.toEvenClifford)⁻¹ := by
      unfold EvenClifford.norm
      ring1
    _ = _ := (ExplicitField.div_eq_mul_inv _ _).symm

/-- A nonzero original Clifford scalar certifies that its rotation anchor is defined. -/
theorem anchorDefinedOfScalarNonzero (value : form.NonNullEvenClifford)
    (scalarNonzero : value.toEvenClifford.scalar ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (actionRotation value).anchorDenominator ≠ 0 := by
  rw [value.anchorDenominator_actionRotation]
  have scalarSquareNonzero : value.toEvenClifford.scalar ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  exact ExplicitField.div_ne_zero
    (ExplicitField.mul_ne_zero (four_ne_zero twoNonzero) scalarSquareNonzero) value.normNonzero

/-- A Clifford rotation's anchor is the skew matrix of its scalar-normalized original vector.

The original cap-normalization builder retains the vector divided by the
supplied nonzero scalar. Its action equality transports the computed
anchor without choosing a new homogeneous representative.
-/
theorem anchor_actionRotation (value : form.NonNullEvenClifford)
    (scalarNonzero : value.toEvenClifford.scalar ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (actionRotation value).anchor (value.anchorDefinedOfScalarNonzero scalarNonzero twoNonzero) =
      form.actionSkew (Vector3.scale value.toEvenClifford.scalar⁻¹ value.toEvenClifford.vector) := by
  let normalization := Cayley.TernaryForm.capNormalization form value scalarNonzero
  have computed := congrArg
    (fun rotation : form.SpecialOrthogonal => Matrix3.scale rotation.anchorDenominator⁻¹
      (Matrix3.sub rotation.matrix rotation.inverseMatrix)) normalization.actionRotation_eq
  exact computed.symm.trans
    (Form.SpecialOrthogonal.anchor_capRotation normalization.anchor normalization.defined twoNonzero)

/-- Two pure half-turn representatives have nonzero product scalar when their axes pair nontrivially. -/
theorem halfTurnProduct_scalar_ne_zero (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (pairingNonzero : form.bilinear first second ≠ 0) :
    (NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
      (NonNullEvenClifford.halfTurnValue form second secondNonNull)).toEvenClifford.scalar ≠ 0 := by
  have productNonzero := ExplicitField.mul_ne_zero form.determinantNonzero pairingNonzero
  change 0 * 0 - form.determinant * form.bilinear first second ≠ 0
  intro zeroScalar
  apply productNonzero
  calc
    _ = -(0 * 0 - form.determinant * form.bilinear first second) := by ring1
    _ = 0 := by rw [zeroScalar]; ring1

/-- The anchor of two pure half-turn representatives is their determinant-normalized cross skew matrix.

The original product has scalar minus determinant times pairing and vector
minus the form cross. Scalar normalization cancels the two signs, leaving
the form cross divided by determinant times pairing.
-/
theorem anchor_halfTurnProduct (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (pairingNonzero : form.bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
      (NonNullEvenClifford.halfTurnValue form second secondNonNull)
    (actionRotation value).anchor (value.anchorDefinedOfScalarNonzero
        (halfTurnProduct_scalar_ne_zero first second firstNonNull secondNonNull pairingNonzero) twoNonzero) =
      form.actionSkew (Vector3.scale (form.determinant * form.bilinear first second)⁻¹
        (form.cliffordCross first second)) := by
  let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
    (NonNullEvenClifford.halfTurnValue form second secondNonNull)
  have scalar : value.toEvenClifford.scalar = -(form.determinant * form.bilinear first second) := by
    change 0 * 0 - form.determinant * form.bilinear first second = _
    ring1
  have vector : value.toEvenClifford.vector = Vector3.neg (form.cliffordCross first second) := by
    change Vector3.sub (Vector3.add (Vector3.scale 0 second) (Vector3.scale 0 first))
      (form.cliffordCross first second) = _
    ext <;> unfold Vector3.sub Vector3.add Vector3.scale Vector3.neg <;> ring1
  have normalized : Vector3.scale value.toEvenClifford.scalar⁻¹ value.toEvenClifford.vector =
      Vector3.scale (form.determinant * form.bilinear first second)⁻¹ (form.cliffordCross first second) := by
    rw [scalar, vector, ExplicitField.inv_neg]
    ext <;> unfold Vector3.scale Vector3.neg <;> ring1
  exact (value.anchor_actionRotation
    (halfTurnProduct_scalar_ne_zero first second firstNonNull secondNonNull pairingNonzero) twoNonzero).trans
      (congrArg form.actionSkew normalized)

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullEvenClifford

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Nontrivially paired non-null normals give a reflection product with a defined rotation anchor. -/
theorem reflectionProduct_anchorDefined (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (pairingNonzero : form.bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (form.reflectionProductRotation first second firstNonNull secondNonNull).anchorDenominator ≠ 0 := by
  let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
    (NonNullEvenClifford.halfTurnValue form second secondNonNull)
  have represents : NonNullEvenClifford.actionRotation value =
      form.reflectionProductRotation first second firstNonNull secondNonNull :=
    (NonNullEvenClifford.halfTurnRotation_mul form first second firstNonNull secondNonNull).symm.trans
      (form.halfTurnRotation_mul first second firstNonNull secondNonNull)
  have defined := value.anchorDefinedOfScalarNonzero
    (TernaryForm.NonNullEvenClifford.halfTurnProduct_scalar_ne_zero
      first second firstNonNull secondNonNull pairingNonzero) twoNonzero
  intro zeroDenominator
  exact defined ((congrArg SpecialOrthogonal.anchorDenominator represents).trans zeroDenominator)

/-- The anchor of two reflections is the skew matrix of their determinant-normalized form cross.

The original product rotation agrees with the product of its two pure
half-turn Clifford representatives. The shared scalar-normalization law
therefore gives the matrix anchor directly from the retained normals.
-/
theorem reflectionProduct_anchor (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (pairingNonzero : form.bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (form.reflectionProductRotation first second firstNonNull secondNonNull).anchor
        (form.reflectionProduct_anchorDefined first second firstNonNull secondNonNull pairingNonzero twoNonzero) =
      form.actionSkew (Vector3.scale (form.determinant * form.bilinear first second)⁻¹
        (form.cliffordCross first second)) := by
  let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
    (NonNullEvenClifford.halfTurnValue form second secondNonNull)
  have represents : NonNullEvenClifford.actionRotation value =
      form.reflectionProductRotation first second firstNonNull secondNonNull :=
    (NonNullEvenClifford.halfTurnRotation_mul form first second firstNonNull secondNonNull).symm.trans
      (form.halfTurnRotation_mul first second firstNonNull secondNonNull)
  have computed := congrArg (fun rotation : form.SpecialOrthogonal =>
    Matrix3.scale rotation.anchorDenominator⁻¹ (Matrix3.sub rotation.matrix rotation.inverseMatrix)) represents
  exact computed.symm.trans (TernaryForm.NonNullEvenClifford.anchor_halfTurnProduct
    first second firstNonNull secondNonNull pairingNonzero twoNonzero)

/-- Construct the second mirror normal from a cap axis and a supplied first normal.

The result is the first normal plus the adjugate cross of the axis with
that normal, equivalently its row action by identity plus the axis skew.
-/
@[expose] def capSecondMirror (form : TernaryForm K) (axis first : Vector3 K) : Vector3 K :=
  Vector3.add first (form.cliffordCross axis first)

/-- The cap's second mirror normal is the first acted on by identity plus its skew matrix. -/
theorem capSecondMirror_eq_rowMul (form : TernaryForm K) (axis first : Vector3 K) :
    form.capSecondMirror axis first = Matrix3.rowMul first (Matrix3.add Matrix3.identity (form.actionSkew axis)) := by
  rw [Matrix3.rowMul_add, Matrix3.rowMul_identity, form.rowMul_actionSkew]
  rfl

/-- The first and constructed cap normals pair to the original first quadrance. -/
theorem bilinear_capSecondMirror (form : TernaryForm K) (axis first : Vector3 K) :
    form.bilinear first (form.capSecondMirror axis first) = form.quadrance first := by
  unfold capSecondMirror
  rw [form.bilinear_add_right, form.bilinear_comm first (form.cliffordCross axis first),
    form.cliffordCross_perpendicular_right]
  change form.bilinear first first + 0 = form.bilinear first first
  ring1

/-- A perpendicular first normal gives the second cap normal's exact quadrance. -/
theorem quadrance_capSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (perpendicular : form.Perpendicular first axis) :
    form.quadrance (form.capSecondMirror axis first) =
      form.quadrance first * Cayley.TernaryForm.cayleyDenominator form axis := by
  unfold capSecondMirror
  rw [form.quadrance_add, form.bilinear_comm first (form.cliffordCross axis first),
    form.cliffordCross_perpendicular_right, form.quadrance_cliffordCross,
    form.bilinear_comm axis first, perpendicular]
  unfold Cayley.TernaryForm.cayleyDenominator
  ring1

/-- A defined cap and a non-null perpendicular first normal give a non-null second normal. -/
theorem capSecondMirror_nonNull (form : TernaryForm K) (axis first : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0)
    (firstNonNull : form.quadrance first ≠ 0) (perpendicular : form.Perpendicular first axis) :
    form.quadrance (form.capSecondMirror axis first) ≠ 0 := by
  rw [form.quadrance_capSecondMirror axis first perpendicular]
  exact ExplicitField.mul_ne_zero firstNonNull defined

/-- The cross of the first and constructed cap normals is the determinant-weighted first quadrance times the axis. -/
theorem cliffordCross_capSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (perpendicular : form.Perpendicular first axis) :
    form.cliffordCross first (form.capSecondMirror axis first) =
      Vector3.scale (form.determinant * form.quadrance first) axis := by
  unfold capSecondMirror
  rw [form.cliffordCross_add_right, form.cliffordCross_self, form.cliffordCross_vector_triple, perpendicular]
  ext <;> unfold Vector3.add Vector3.zero Vector3.sub Vector3.scale TernaryForm.quadrance <;> ring1

/-- Every non-null perpendicular first mirror yields a two-reflection factorization of the original cap.

The ordered product of the two pure Clifford representatives is the cap
representative scaled by minus the determinant times the first quadrance.
That retained nonzero scale preserves its action, including null cap axes.
-/
theorem reflectionProduct_capSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0)
    (firstNonNull : form.quadrance first ≠ 0) (perpendicular : form.Perpendicular first axis) :
    form.reflectionProductRotation first (form.capSecondMirror axis first) firstNonNull
        (form.capSecondMirror_nonNull axis first defined firstNonNull perpendicular) =
      Cayley.TernaryForm.capRotation form axis defined := by
  let second := form.capSecondMirror axis first
  let secondNonNull := form.capSecondMirror_nonNull axis first defined firstNonNull perpendicular
  let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
    (NonNullEvenClifford.halfTurnValue form second secondNonNull)
  have factorNonzero : -(form.determinant * form.quadrance first) ≠ 0 := by
    intro zero
    have productNonzero := ExplicitField.mul_ne_zero form.determinantNonzero firstNonNull
    apply productNonzero
    calc
      _ = -(-(form.determinant * form.quadrance first)) := by ring1
      _ = 0 := by rw [zero]; ring1
  have equivalent : NonNullEvenClifford.Equivalent (Cayley.TernaryForm.capValue form axis defined) value := by
    refine ⟨-(form.determinant * form.quadrance first), factorNonzero, ?_⟩
    apply EvenClifford.ext
    · change 0 * 0 - form.determinant * form.bilinear first second =
        -(form.determinant * form.quadrance first) * 1
      rw [form.bilinear_capSecondMirror]
      ring1
    · change Vector3.sub (Vector3.add (Vector3.scale 0 second) (Vector3.scale 0 first))
        (form.cliffordCross first second) = Vector3.scale (-(form.determinant * form.quadrance first)) axis
      rw [form.cliffordCross_capSecondMirror axis first perpendicular]
      ext <;> unfold Vector3.sub Vector3.add Vector3.scale <;> ring1
  calc
    _ = NonNullEvenClifford.actionRotation value :=
      (form.halfTurnRotation_mul first second firstNonNull secondNonNull).symm.trans
        (NonNullEvenClifford.halfTurnRotation_mul form first second firstNonNull secondNonNull)
    _ = _ := (NonNullEvenClifford.actionRotation_respects_equivalent equivalent).symm

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

namespace Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

variable {K : Type*} [ExplicitField K] [DecidableEq K] {form : Form K} {rotation : form.SpecialOrthogonal}

/-- The anchor computed from the original rotation equals the skew matrix of its retained cap normalization.

The original axis witness supplies its cached Clifford normalization and
exact cap-recovery certificate. Transporting the computed matrix along
that equality retains the same normalization and axis.
-/
theorem anchor_recovery (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0) (notHalfTurn : rotationHalfSpread form rotation ≠ 1) :
    rotation.anchor ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn) =
      form.actionSkew (witness.capNormalizationOfHalfSpreadNeOne twoNonzero notHalfTurn).anchor := by
  let normalization := witness.capNormalizationOfHalfSpreadNeOne twoNonzero notHalfTurn
  have recovery : capRotation form normalization.anchor normalization.defined = rotation :=
    witness.cap_recovery twoNonzero notHalfTurn
  have computed := congrArg
    (fun value : form.SpecialOrthogonal => Matrix3.scale value.anchorDenominator⁻¹
      (Matrix3.sub value.matrix value.inverseMatrix)) recovery
  exact computed.symm.trans
    (Form.SpecialOrthogonal.anchor_capRotation normalization.anchor normalization.defined twoNonzero)

end Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness

end
