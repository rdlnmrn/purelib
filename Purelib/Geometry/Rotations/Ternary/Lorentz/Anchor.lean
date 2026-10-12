module

public import Purelib.Geometry.Rotations.Ternary.Cayley.Anchor
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Cayley
import Purelib.Geometry.Quadratic.Ternary.Lorentz
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Lorentz
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Vector anchors of time-first Lorentz rotations

The original Lorentz vector readback extracts the anchor vector from the
shared computed matrix anchor. Its cap reconstructs the same rotation,
and the retained vector supplies the fixed direction and half twist.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The Lorentz adjoint of a rotation is its original retained inverse matrix. -/
theorem adjoint_rotation (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    Quadratic.Ternary.Lorentz.adjoint oneNonzero rotation.matrix = rotation.inverseMatrix := by
  unfold Quadratic.Ternary.Lorentz.adjoint
  rw [rotation.inverseMatrix_eq_transpose_conjugate, Form.lorentz_inverse]

/-- The shared antisymmetric part equals half the difference from the Lorentz adjoint. -/
theorem antisymmetricPart_eq_adjointFormula (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    rotation.antisymmetricPart twoNonzero = Matrix3.scale (1 / 2)
      (Matrix3.sub rotation.matrix (Quadratic.Ternary.Lorentz.adjoint oneNonzero rotation.matrix)) := by
  unfold Form.SpecialOrthogonal.antisymmetricPart
  rw [adjoint_rotation, ExplicitField.div_eq_mul_inv, one_mul]

/-- Recover a Lorentz anchor from the literal adjoint-antisymmetric part and one division by one plus trace. -/
theorem rotationAnchor_eq_adjointFormula (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    rotation.anchor defined = Matrix3.scale (2 / (1 + Matrix3.trace rotation.matrix))
      (Matrix3.scale (1 / 2)
        (Matrix3.sub rotation.matrix (Quadratic.Ternary.Lorentz.adjoint oneNonzero rotation.matrix))) := by
  change rotation.anchor defined = Matrix3.scale (2 / rotation.anchorDenominator) _
  rw [rotation.anchor_eq_antisymmetricPart defined twoNonzero,
    antisymmetricPart_eq_adjointFormula oneNonzero rotation twoNonzero]

/-- The computed anchor of a Lorentz rotation has negative metrical adjoint.

The shared form-skew certificate becomes the Lorentz adjoint relation
after multiplication by the original Lorentz metric, whose square is
the identity matrix.
-/
theorem rotationAnchor_isAnchor (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) :
    Quadratic.Ternary.Lorentz.IsAnchor oneNonzero (rotation.anchor defined) := by
  unfold Quadratic.Ternary.Lorentz.IsAnchor Quadratic.Ternary.Lorentz.adjoint
  calc
    _ = Matrix3.mul (Matrix3.transpose
        (Matrix3.mul (rotation.anchor defined) (Form.lorentz oneNonzero).matrix))
        (Form.lorentz oneNonzero).matrix := by
      rw [Matrix3.transpose_mul, (Form.lorentz oneNonzero).symmetric]
    _ = Matrix3.mul (Matrix3.neg
        (Matrix3.mul (rotation.anchor defined) (Form.lorentz oneNonzero).matrix))
        (Form.lorentz oneNonzero).matrix := by rw [rotation.anchor_mul_form_antisymmetric]
    _ = Matrix3.neg (Matrix3.mul
        (Matrix3.mul (rotation.anchor defined) (Form.lorentz oneNonzero).matrix)
        (Form.lorentz oneNonzero).matrix) := by
      ext <;> unfold Matrix3.neg Matrix3.mul <;> ring1
    _ = _ := by rw [Matrix3.mul_assoc, Form.lorentz_matrix_square, Matrix3.mul_identity]

/-- Read the original time-first Lorentz vector from a rotation's computed matrix anchor. -/
@[expose] def rotationAnchorVector (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) : Vector3 K :=
  Quadratic.Ternary.Lorentz.anchorVector (rotation.anchor defined)

/-- The read-back vector reconstructs the computed Lorentz anchor matrix. -/
theorem anchor_rotationAnchorVector (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Quadratic.Ternary.Lorentz.anchor oneNonzero (rotationAnchorVector oneNonzero rotation defined) =
      rotation.anchor defined :=
  Quadratic.Ternary.Lorentz.anchor_anchorVector oneNonzero (rotation.anchor defined) twoNonzero
    (rotationAnchor_isAnchor oneNonzero rotation defined)

/-- The original Lorentz vector readback uniquely determines a rotation's matrix anchor. -/
theorem rotationAnchorVector_unique (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (vector : Vector3 K)
    (represents : Quadratic.Ternary.Lorentz.anchor oneNonzero vector = rotation.anchor defined) :
    vector = rotationAnchorVector oneNonzero rotation defined :=
  (Quadratic.Ternary.Lorentz.anchorVector_anchor oneNonzero vector).symm.trans
    (congrArg (Quadratic.Ternary.Lorentz.anchorVector (K := K)) represents)

/-- The Lorentz vector anchor of a cap is its original supplied vector. -/
theorem rotationAnchorVector_cap (axis : Vector3 K) (defined : capDenominator oneNonzero axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchorVector oneNonzero (capRotation oneNonzero axis defined)
        (((capRotation oneNonzero axis defined).anchorDenominator_ne_zero_iff twoNonzero).mpr
          (halfSpread_cap_ne_one oneNonzero axis defined twoNonzero)) = axis := by
  unfold rotationAnchorVector
  have recovered : (capRotation oneNonzero axis defined).anchor
        (((capRotation oneNonzero axis defined).anchorDenominator_ne_zero_iff twoNonzero).mpr
          (halfSpread_cap_ne_one oneNonzero axis defined twoNonzero)) =
      Quadratic.Ternary.Lorentz.anchor oneNonzero axis :=
    Form.SpecialOrthogonal.anchor_capRotation (Vector3.neg axis)
      (by rw [cayleyDenominator_neg]; exact defined) twoNonzero
  rw [recovered]
  exact Quadratic.Ternary.Lorentz.anchorVector_anchor oneNonzero axis

/-- The computed Lorentz anchor vector is the negative of the cached generic cap normalization.

The witness retains the original rotation and its Clifford normalization.
The negative sign converts that generic skew coordinate to the paper's
time-first Lorentz vector coordinate.
-/
theorem rotationAnchorVector_eq_neg_normalization [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (witness : Cayley.TernaryForm.RotationAxisSpreadWitness (Form.lorentz oneNonzero) rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn) =
      Vector3.neg (witness.capNormalizationOfHalfSpreadNeOne twoNonzero notHalfTurn).anchor := by
  let normalization := witness.capNormalizationOfHalfSpreadNeOne twoNonzero notHalfTurn
  have convert : (Form.lorentz oneNonzero).actionSkew normalization.anchor =
      Quadratic.Ternary.Lorentz.anchor oneNonzero (Vector3.neg normalization.anchor) := by
    unfold Quadratic.Ternary.Lorentz.anchor
    rw [Vector3.neg_neg]
  calc
    _ = Quadratic.Ternary.Lorentz.anchorVector
        ((Form.lorentz oneNonzero).actionSkew normalization.anchor) :=
      congrArg (Quadratic.Ternary.Lorentz.anchorVector (K := K))
        (witness.anchor_recovery twoNonzero notHalfTurn)
    _ = Quadratic.Ternary.Lorentz.anchorVector
        (Quadratic.Ternary.Lorentz.anchor oneNonzero (Vector3.neg normalization.anchor)) :=
      congrArg (Quadratic.Ternary.Lorentz.anchorVector (K := K)) convert
    _ = _ := Quadratic.Ternary.Lorentz.anchorVector_anchor oneNonzero _

/-- The computed Lorentz vector lies in the cap domain and its cap recovers the original rotation.

One cached axis witness supplies the generic normalization. The vector
readback identifies its negative with the computed Lorentz anchor vector,
transporting both the original denominator certificate and cap equality.
The recovered cap is independent of which proof of its domain is supplied.
-/
theorem rotationAnchorVector_cap_recovery [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    let vector := rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    capDenominator oneNonzero vector ≠ 0 ∧
      ∀ defined : capDenominator oneNonzero vector ≠ 0, capRotation oneNonzero vector defined = rotation := by
  let witness := Cayley.TernaryForm.rotationAxisSpreadWitness (Form.lorentz oneNonzero) rotation twoNonzero
  let normalization := witness.capNormalizationOfHalfSpreadNeOne twoNonzero notHalfTurn
  have vectorEq := rotationAnchorVector_eq_neg_normalization oneNonzero rotation witness twoNonzero notHalfTurn
  have denominatorEq : Cayley.TernaryForm.cayleyDenominator (Form.lorentz oneNonzero) normalization.anchor =
      capDenominator oneNonzero (Vector3.neg normalization.anchor) := by
    have equation := cayleyDenominator_neg oneNonzero (Vector3.neg normalization.anchor)
    rw [Vector3.neg_neg] at equation
    exact equation
  have defined : capDenominator oneNonzero
      (rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)) ≠ 0 := by
    rw [vectorEq]
    exact fun zero => normalization.defined (denominatorEq.trans zero)
  refine ⟨defined, ?_⟩
  intro domain
  change Cayley.TernaryForm.capRotation (Form.lorentz oneNonzero)
    (Vector3.neg (rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn))) _ = rotation
  have inputEq := congrArg Vector3.neg vectorEq
  rw [Vector3.neg_neg] at inputEq
  calc
    _ = Cayley.TernaryForm.capRotation (Form.lorentz oneNonzero) normalization.anchor normalization.defined := by
      apply Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
      rw [Form.capRotation_matrix_quadratic, Form.capRotation_matrix_quadratic, inputEq]
    _ = rotation := witness.cap_recovery twoNonzero notHalfTurn

/-- The computed Lorentz anchor vector has nonzero original cap denominator. -/
theorem rotationAnchorVector_defined [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    capDenominator oneNonzero (rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)) ≠ 0 :=
  (rotationAnchorVector_cap_recovery oneNonzero rotation twoNonzero notHalfTurn).1

/-- Taking the cap of the computed Lorentz anchor vector reconstructs the same original rotation. -/
theorem cap_rotationAnchorVector [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    capRotation oneNonzero (rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn))
        (rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn) = rotation :=
  (rotationAnchorVector_cap_recovery oneNonzero rotation twoNonzero notHalfTurn).2 _

/-- Factor an original non-half-turn Lorentz rotation from any non-null first normal perpendicular to its anchor.

The computed second normal is the first plus the signed cross of the
original anchor vector with the first. Its retained non-null certificate
and reflection-product equality reconstruct the original rotation.
-/
@[expose] def reflectionFactorizationFromFirst [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1)
    (first : Vector3 K) (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular first
      (rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn))) :
    let axis := rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    Σ' second : Vector3 K, Σ' secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0,
      second = Vector3.add first (Quadratic.Ternary.Lorentz.cross oneNonzero axis first) ∧
        (Form.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull =
          rotation := by
  let form := Form.lorentz oneNonzero
  let axis := rotationAnchorVector oneNonzero rotation
    ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
  have defined : Cayley.TernaryForm.cayleyDenominator form (Vector3.neg axis) ≠ 0 := by
    rw [cayleyDenominator_neg]
    exact rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn
  have genericPerpendicular : form.Perpendicular first (Vector3.neg axis) := by
    change form.bilinear first (Vector3.neg axis) = 0
    rw [form.bilinear_neg_right, perpendicular]
    ring1
  refine ⟨form.capSecondMirror (Vector3.neg axis) first,
    form.capSecondMirror_nonNull (Vector3.neg axis) first defined firstNonNull genericPerpendicular, ?_, ?_⟩
  · unfold Form.capSecondMirror Quadratic.Ternary.Lorentz.cross
    rw [form.cliffordCross_neg_left]
  · exact (form.reflectionProduct_capSecondMirror
      (Vector3.neg axis) first defined firstNonNull genericPerpendicular).trans
        (cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn)

/-- The computed Lorentz anchor vector is fixed by its original rotation. -/
theorem rowMul_rotationAnchorVector [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    let vector := rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    Matrix3.rowMul vector rotation.matrix = vector := by
  let vector := rotationAnchorVector oneNonzero rotation
    ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
  let defined := rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn
  have fixed : Matrix3.rowMul vector (capRotation oneNonzero vector defined).matrix = vector :=
    rowMul_self_cap oneNonzero vector defined
  rw [cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn] at fixed
  exact fixed

/-- The original quadrance of a Lorentz rotation's anchor vector is its half twist.

The recovered cap has the same original rotation and half spread. Its
quadrance-recovery identity therefore gives `p/(1-p)` for the exact vector
read back from the rotation matrix.
-/
theorem quadrance_rotationAnchorVector [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    (Form.lorentz oneNonzero).quadrance (rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)) =
      Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation /
        (1 - Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation) := by
  have quadrance := quadrance_eq_halfSpread_div_one_sub oneNonzero _
    (rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn) twoNonzero
  rw [cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn] at quadrance
  exact quadrance

/-- The matrix anchor of two Lorentz reflections is the original cross divided by their pairing.

The shared Clifford normalization gives the determinant-normalized generic
cross. The Lorentz determinant is one and its signed cross is the negative
generic cross, which converts the result to the paper's vector anchor.
-/
theorem rotationAnchor_reflectionProduct (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0)
    (pairingNonzero : (Form.lorentz oneNonzero).bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    ((Form.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull).anchor
        ((Form.lorentz oneNonzero).reflectionProduct_anchorDefined
          first second firstNonNull secondNonNull pairingNonzero twoNonzero) =
      Quadratic.Ternary.Lorentz.anchor oneNonzero
        (Vector3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹
          (Quadratic.Ternary.Lorentz.cross oneNonzero first second)) := by
  have conversion : Vector3.scale
        ((Form.lorentz oneNonzero).determinant * (Form.lorentz oneNonzero).bilinear first second)⁻¹
        ((Form.lorentz oneNonzero).cliffordCross first second) =
      Vector3.neg (Vector3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹
        (Quadratic.Ternary.Lorentz.cross oneNonzero first second)) := by
    rw [Form.lorentz_determinant, one_mul]
    unfold Quadratic.Ternary.Lorentz.cross
    ext <;> unfold Vector3.scale Vector3.neg <;> ring1
  exact ((Form.lorentz oneNonzero).reflectionProduct_anchor
    first second firstNonNull secondNonNull pairingNonzero twoNonzero).trans
      (congrArg (Form.lorentz oneNonzero).actionSkew conversion)

/-- The vector readback of a Lorentz reflection-product anchor is its original signed cross over pairing. -/
theorem rotationAnchorVector_reflectionProduct (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0)
    (pairingNonzero : (Form.lorentz oneNonzero).bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchorVector oneNonzero
        ((Form.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull)
        ((Form.lorentz oneNonzero).reflectionProduct_anchorDefined
          first second firstNonNull secondNonNull pairingNonzero twoNonzero) =
      Vector3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹
        (Quadratic.Ternary.Lorentz.cross oneNonzero first second) := by
  unfold rotationAnchorVector
  rw [rotationAnchor_reflectionProduct oneNonzero first second firstNonNull secondNonNull pairingNonzero twoNonzero]
  exact Quadratic.Ternary.Lorentz.anchorVector_anchor oneNonzero _

/-- The anchor of two Lorentz reflections is the antisymmetric difference of their dual outer products over pairing. -/
theorem rotationAnchor_reflectionProduct_outerFormula (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0)
    (pairingNonzero : (Form.lorentz oneNonzero).bilinear first second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    ((Form.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull).anchor
        ((Form.lorentz oneNonzero).reflectionProduct_anchorDefined
          first second firstNonNull secondNonNull pairingNonzero twoNonzero) =
      Matrix3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹
        (Matrix3.sub (Matrix3.outer ((Form.lorentz oneNonzero).dual first) second)
          (Matrix3.outer ((Form.lorentz oneNonzero).dual second) first)) := by
  rw [rotationAnchor_reflectionProduct oneNonzero first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Quadratic.Ternary.Lorentz.anchor_scale]
  have crossOuter : Quadratic.Ternary.Lorentz.anchor oneNonzero
        (Quadratic.Ternary.Lorentz.cross oneNonzero first second) =
      Matrix3.sub (Matrix3.outer ((Form.lorentz oneNonzero).dual first) second)
        (Matrix3.outer ((Form.lorentz oneNonzero).dual second) first) :=
    (Quadratic.Ternary.Lorentz.anchor_commutator oneNonzero second first).symm.trans
      (Quadratic.Ternary.Lorentz.anchor_commutator_outer oneNonzero second first)
  exact congrArg (Matrix3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹) crossOuter

/-- The quadrance of the normalized Lorentz reflection-product anchor is spread over its complement.

Nonzero pairing makes the spread complement nonzero. Cancelling its
original squared pairing converts the cross-quadrance spread identity
to the quadrance of the exact normalized anchor vector.
-/
theorem quadrance_reflectionProductAnchor (first second : Vector3 K)
    (firstNonNull : (Form.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (Form.lorentz oneNonzero).quadrance second ≠ 0)
    (pairingNonzero : (Form.lorentz oneNonzero).bilinear first second ≠ 0) :
    (Form.lorentz oneNonzero).quadrance
        (Vector3.scale ((Form.lorentz oneNonzero).bilinear first second)⁻¹
          (Quadratic.Ternary.Lorentz.cross oneNonzero first second)) =
      (Form.lorentz oneNonzero).spread first second firstNonNull secondNonNull /
        (1 - (Form.lorentz oneNonzero).spread first second firstNonNull secondNonNull) := by
  have complement : 1 - (Form.lorentz oneNonzero).spread first second firstNonNull secondNonNull =
      (Form.lorentz oneNonzero).bilinear first second ^ 2 /
        ((Form.lorentz oneNonzero).quadrance first * (Form.lorentz oneNonzero).quadrance second) := by
    unfold Form.spread
    ring1
  have pairingSquareNonzero : (Form.lorentz oneNonzero).bilinear first second ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero pairingNonzero pairingNonzero
  have complementNonzero : 1 - (Form.lorentz oneNonzero).spread first second firstNonNull secondNonNull ≠ 0 := by
    rw [complement]
    exact ExplicitField.div_ne_zero pairingSquareNonzero (ExplicitField.mul_ne_zero firstNonNull secondNonNull)
  apply ExplicitField.eq_of_mul_eq_mul_right complementNonzero
  rw [ExplicitField.div_mul_cancel _ complementNonzero, Form.quadrance_scale, complement,
    Quadratic.Ternary.Lorentz.spread_eq_cross_quadrance]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    _ = (((Form.lorentz oneNonzero).bilinear first second) *
        ((Form.lorentz oneNonzero).bilinear first second)⁻¹) ^ 2 *
        (Form.lorentz oneNonzero).quadrance (Quadratic.Ternary.Lorentz.cross oneNonzero first second) *
        ((Form.lorentz oneNonzero).quadrance first * (Form.lorentz oneNonzero).quadrance second)⁻¹ := by ring1
    _ = _ := by rw [ExplicitField.mul_inv_cancel _ pairingNonzero]; ring1

end Purelib.Geometry.Rotations.Ternary.Lorentz

end
