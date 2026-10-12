module

public import Purelib.Algebra.Quadratic.Ternary.Euclidean
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Ternary.Clifford
public import Purelib.Geometry.Rotations.Ternary.Cayley.HalfTurn
import Purelib.Geometry.Rotations.Ternary.Cayley.Spread
public import Purelib.Geometry.Rotations.Spread
import Purelib.Geometry.Rotations.Reflection
import Purelib.Geometry.Rotations.Cayley.FieldRealizations
import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Quadratic.Space3.Ordered
public import Purelib.Algebra.Field.Characteristic.Nonzero
public import Purelib.Polynomial.Quadratic.Reciprocal
public import Purelib.LinearAlgebra.Coordinates3.Eigenvector
import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Euclidean rotations as rotations of the identity form

The retained matrix and its transpose satisfy the form-indexed rotation
contract. The shared constructive fixed-direction builder then applies to
the original Euclidean rotation, with no new vector representation.
-/

public section

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Characteristic.Nonzero
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Basic (Rotation)
open Purelib.Geometry.Quadratic.Space3
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField OrderDifferenceLaw)
open Purelib.Polynomial.Quadratic

namespace Purelib.Geometry.Rotations.Basic.Rotation

variable {K : Type*} [ExplicitField K]

/-- Retain a Euclidean rotation as a special orthogonal matrix of the identity form.

The forward matrix is unchanged, and its transpose is the cached inverse.
The original orthogonality and determinant-one proofs certify the form-indexed
rotation; the supplied nonzero unit certifies the form's nondegeneracy.
-/
@[expose] def toTernary (rotation : Rotation K) (oneNonzero : (1 : K) ≠ 0) :
    (TernaryForm.euclidean oneNonzero).SpecialOrthogonal where
  matrix := rotation.matrix
  inverseMatrix := Matrix3.transpose rotation.matrix
  matrix_mul_inverse := rotation.orthogonal
  inverse_mul_matrix := Matrix3.inverse_mul_of_mul_eq_identity oneNonzero rotation.orthogonal
  preservesMatrix := by
    change Matrix3.mul (Matrix3.mul rotation.matrix Matrix3.identity)
      (Matrix3.transpose rotation.matrix) = Matrix3.identity
    rw [Matrix3.mul_identity]
    exact rotation.orthogonal
  determinantOne := rotation.determinantOne

/-- The form-indexed Euclidean view preserves the exact original rotation matrix. -/
theorem toTernary_matrix (rotation : Rotation K) (oneNonzero : (1 : K) ≠ 0) :
    (rotation.toTernary oneNonzero).matrix = rotation.matrix := rfl

/-- Construct a nonzero fixed direction of an original Euclidean rotation.

The identity-form view retains the original matrix. Nonzero two and executable
scalar equality supply the shared two-half-turn construction, including its
nonzero fallback in the identity case.
-/
@[expose] def fixedDirection [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector rotation.matrix = vector :=
  let oneNonzero := one_ne_zero_of_nonzero twoNonzero
  (TernaryForm.euclidean oneNonzero).fixedDirection (rotation.toTernary oneNonzero) twoNonzero

/-- The identity-form view of an original Euclidean half turn has the same half-turn matrix. -/
theorem toTernary_halfTurn_matrix (axis : Vector3 K) (nonNull : Vector3.quadrance axis ≠ 0)
    (oneNonzero : (1 : K) ≠ 0) :
    ((Reflection.halfTurnRotation axis nonNull).toTernary oneNonzero).matrix =
      (TernaryForm.euclidean oneNonzero).halfTurn axis
        (by rw [TernaryForm.quadrance_euclidean]; exact nonNull) := by
  change Reflection.halfTurn axis nonNull = _
  unfold TernaryForm.halfTurn TernaryForm.reflection Reflection.halfTurn Reflection.reflection
  rw [TernaryForm.dual_euclidean, TernaryForm.quadrance_euclidean]

/-- Construct a non-null half-turn axis when the original Euclidean half spread is one.

The identity-form view retains the original rotation matrix. The shared
Clifford boundary construction supplies the axis, and the matrix comparison
returns the original Euclidean half-turn equality.
-/
@[expose] def halfTurnWitness [DecidableEq K] (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Spread.halfSpread rotation = 1) :
    Σ' axis : Vector3 K, Σ' nonNull : Vector3.quadrance axis ≠ 0,
      Reflection.halfTurnRotation axis nonNull = rotation := by
  let oneNonzero := one_ne_zero_of_nonzero twoNonzero
  let form := TernaryForm.euclidean oneNonzero
  let witness := Ternary.Cayley.TernaryForm.halfTurnWitness form
    (rotation.toTernary oneNonzero) twoNonzero halfSpreadOne
  have axisNonNull : Vector3.quadrance witness.1 ≠ 0 := by
    intro axisNull
    apply witness.2.1
    rw [TernaryForm.quadrance_euclidean]
    exact axisNull
  refine ⟨witness.1, axisNonNull, ?_⟩
  apply Rotation.eq_of_matrix_eq
  have matrixEqual := congrArg (fun result : form.SpecialOrthogonal => result.matrix) witness.2.2
  calc
    _ = ((Reflection.halfTurnRotation witness.1 axisNonNull).toTernary oneNonzero).matrix := rfl
    _ = form.halfTurn witness.1 _ := toTernary_halfTurn_matrix witness.1 axisNonNull oneNonzero
    _ = rotation.matrix := matrixEqual

/-- Original Euclidean half spread one is equivalent to a non-null half-turn representation. -/
theorem halfSpread_eq_one_iff_halfTurn [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread rotation = 1 ↔
      ∃ axis : Vector3 K, ∃ nonNull : Vector3.quadrance axis ≠ 0,
        Reflection.halfTurnRotation axis nonNull = rotation := by
  constructor
  · intro halfSpreadOne
    let witness := rotation.halfTurnWitness twoNonzero halfSpreadOne
    exact ⟨witness.1, witness.2.1, witness.2.2⟩
  · rintro ⟨axis, nonNull, represents⟩
    rw [← represents]
    exact Spread.halfSpread_halfTurn axis nonNull twoNonzero

/-- The half spread of a squared original Euclidean rotation equals its canonical spread.

The identity-form view preserves both forward matrices in the product.
The shared ternary Newton-identity proof therefore gives the original
Euclidean half-spread law without changing rotation owners.
-/
theorem halfSpread_square (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Rotation.mul rotation rotation) = Spread.rotationSpread rotation :=
  Ternary.Cayley.TernaryForm.rotationHalfSpread_square
    (TernaryForm.euclidean (one_ne_zero_of_nonzero twoNonzero))
    (rotation.toTernary (one_ne_zero_of_nonzero twoNonzero)) twoNonzero

/-- A Euclidean rotation with half spread strictly between zero and one has no field eigenvalue other than one.

The retained ordered difference law makes the original reciprocal factor's
discriminant negative. A nonzero eigenvector of the original rotation matrix
therefore forces the characteristic polynomial's linear factor to vanish.
-/
theorem eigenvalue_eq_one_of_halfSpread_unit_interval {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (law : OrderDifferenceLaw F)
    (positive : 0 < Spread.halfSpread rotation) (belowOne : Spread.halfSpread rotation < 1)
    (point : F) (witness : Matrix3.RowEigenvector rotation.matrix point) : point = 1 := by
  letI : DecidableEq F := OrderedExplicitField.eq_decidable
  have negative := Reciprocal.discriminant_halfSpread_negative law (Spread.halfSpread rotation) positive belowOne
  have reciprocalNonzero := Reciprocal.eval_ne_zero_of_discriminant_negative law _ negative point
  have characteristic := witness.characteristicValue_eq_zero
  rw [Spread.characteristicValue_rotation rotation RayOrderedExplicitField.two_ne_zero point] at characteristic
  have linearZero : point - 1 = 0 := ExplicitField.eq_zero_of_mul_eq_zero_right reciprocalNonzero characteristic
  calc
    point = point - 1 + 1 := by ring1
    _ = 1 := by rw [linearZero, zero_add]

/-- An ordered nonidentity Euclidean rotation away from half turns has half spread strictly between zero and one.

The original rotation is reconstructed from its recovered anchor. That
anchor is nonzero because a zero anchor gives identity, and its positive
Euclidean quadrance gives the lower bound. The original positive cap
denominator and unit complement give the upper bound.
-/
theorem halfSpread_unit_interval_of_nonidentity_notHalfTurn {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (law : OrderDifferenceLaw F)
    (notIdentity : rotation.matrix ≠ Matrix3.identity) (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    0 < Spread.halfSpread rotation ∧ Spread.halfSpread rotation < 1 := by
  let axis := Axis.Recovery.rotationAnchorVector rotation notHalfTurn
  let defined := Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn RayOrderedExplicitField.two_ne_zero
  have matrix := Axis.Recovery.cap_rotationAnchor rotation notHalfTurn RayOrderedExplicitField.two_ne_zero
  have axisNonzero : axis ≠ Vector3.zero := by
    intro zero
    apply notIdentity
    calc
      rotation.matrix = Cayley.Cap.cap axis defined := matrix.symm
      _ = Matrix3.identity := by
        have zeroCap := Cayley.FieldRealizations.cap_zero_eq_identity
          (Cayley.FieldRealizations.OrderedFieldClaims.capDenominatorNonzero (Vector3.zero : Vector3 F))
        unfold Cayley.Cap.cap at zeroCap ⊢
        rw [zero]
        exact zeroCap
  have rotationEq : rotation = Cayley.Cap.capRotation axis defined := eq_of_matrix_eq rotation _ matrix.symm
  rw [rotationEq]
  constructor
  · rw [Spread.halfSpread_cap axis defined RayOrderedExplicitField.two_ne_zero, ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct
      (Ordered.OrderedFieldClaims.vectorQuadrancePositive axis axisNonzero)
      (OrderedExplicitField.inv_pos_direct (Cayley.FieldRealizations.OrderedFieldClaims.capDenominatorPositive axis))
  · exact (Cayley.FieldRealizations.OrderedFieldClaims.halfSpread_cap_unit_interval law axis defined
      RayOrderedExplicitField.two_ne_zero).2

/-- An ordered Euclidean rotation other than identity and the half turns has no field eigenvalue other than one. -/
theorem eigenvalue_eq_one_of_nonidentity_notHalfTurn {F : Type*} [RayOrderedExplicitField F]
    (rotation : Rotation F) (law : OrderDifferenceLaw F)
    (notIdentity : rotation.matrix ≠ Matrix3.identity) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (point : F) (witness : Matrix3.RowEigenvector rotation.matrix point) : point = 1 := by
  have interval := rotation.halfSpread_unit_interval_of_nonidentity_notHalfTurn law notIdentity notHalfTurn
  exact rotation.eigenvalue_eq_one_of_halfSpread_unit_interval law interval.1 interval.2 point witness

end Purelib.Geometry.Rotations.Basic.Rotation

namespace Purelib.Geometry.Rotations.Reflection

variable {K : Type*} [ExplicitField K]

/-- The identity-form reflection is the original Euclidean reflection matrix.

The form dual and quadrance reduce to the original vector and quadrance,
preserving the supplied non-null normal and the displayed reflection formula.
-/
theorem reflection_eq_euclidean (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (oneNonzero : (1 : K) ≠ 0) :
    reflection axis nonNull = (TernaryForm.euclidean oneNonzero).reflection axis
      (by rw [TernaryForm.quadrance_euclidean]; exact nonNull) := by
  unfold reflection TernaryForm.reflection
  rw [TernaryForm.dual_euclidean, TernaryForm.quadrance_euclidean]

/-- A Euclidean half turn is determined by fixing its axis and negating its perpendicular plane.

The identity-form view transfers the shared matrix uniqueness proof to the
original Euclidean half turn, retaining the supplied axis and non-nullity.
-/
theorem halfTurn_unique (axis : Vector3 K) (nonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix3 K)
    (fixesAxis : Matrix3.rowMul axis matrix = axis)
    (negatesPerpendicular : ∀ vector : Vector3 K, vector.Perpendicular axis →
      Matrix3.rowMul vector matrix = Vector3.neg vector) : matrix = halfTurn axis nonNull := by
  let oneNonzero := one_ne_zero_of_nonzero twoNonzero
  let form := TernaryForm.euclidean oneNonzero
  have axisNonNull : form.quadrance axis ≠ 0 := by
    rw [TernaryForm.quadrance_euclidean]
    exact nonNull
  have unique := form.halfTurn_unique axis axisNonNull matrix fixesAxis (by
    intro vector perpendicular
    change form.bilinear vector axis = 0 at perpendicular
    rw [TernaryForm.bilinear_euclidean] at perpendicular
    exact negatesPerpendicular vector perpendicular)
  have sameMatrix := Rotation.toTernary_halfTurn_matrix axis nonNull oneNonzero
  change halfTurn axis nonNull = form.halfTurn axis axisNonNull at sameMatrix
  exact unique.trans sameMatrix.symm

/-- The fixed vectors of the original Euclidean half turn are their projections onto its axis.

The coefficient is the original vector dot product divided by the retained
nonzero axis quadrance. The characterization includes the zero vector.
-/
theorem rowMul_halfTurn_eq_self_iff_projection (axis : Vector3 K)
    (nonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K) :
    Matrix3.rowMul vector (halfTurn axis nonNull) = vector ↔
      vector = Vector3.scale (vector.dot axis / axis.quadrance) axis := by
  let oneNonzero := one_ne_zero_of_nonzero twoNonzero
  let form := TernaryForm.euclidean oneNonzero
  have axisNonNull : form.quadrance axis ≠ 0 := by
    rw [TernaryForm.quadrance_euclidean]
    exact nonNull
  have sameMatrix := Rotation.toTernary_halfTurn_matrix axis nonNull oneNonzero
  change halfTurn axis nonNull = form.halfTurn axis axisNonNull at sameMatrix
  constructor
  · intro fixed
    have fixedForm : Matrix3.rowMul vector (form.halfTurn axis axisNonNull) = vector :=
      (congrArg (Matrix3.rowMul vector) sameMatrix).symm.trans fixed
    have projected := (form.rowMul_halfTurn_eq_self_iff_projection
      axis axisNonNull twoNonzero vector).mp fixedForm
    rw [TernaryForm.bilinear_euclidean, TernaryForm.quadrance_euclidean] at projected
    exact projected
  · intro projected
    have projectedForm :
        vector = Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis := by
      rw [TernaryForm.bilinear_euclidean, TernaryForm.quadrance_euclidean]
      exact projected
    exact (congrArg (Matrix3.rowMul vector) sameMatrix).trans
      ((form.rowMul_halfTurn_eq_self_iff_projection axis axisNonNull twoNonzero vector).mpr projectedForm)

/-- Two original Euclidean half turns agree exactly when their non-null axis lines agree.

The shared line comparison retains a nonzero scalar expressing the second
axis in terms of the first, rather than identifying their vector owners.
-/
theorem halfTurn_eq_iff_same_line (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfTurn first firstNonNull = halfTurn second secondNonNull ↔
      ∃ factor : K, factor ≠ 0 ∧ second = Vector3.scale factor first := by
  let oneNonzero := one_ne_zero_of_nonzero twoNonzero
  let form := TernaryForm.euclidean oneNonzero
  have firstFormNonNull : form.quadrance first ≠ 0 := by
    rw [TernaryForm.quadrance_euclidean]
    exact firstNonNull
  have secondFormNonNull : form.quadrance second ≠ 0 := by
    rw [TernaryForm.quadrance_euclidean]
    exact secondNonNull
  have firstMatrix := Rotation.toTernary_halfTurn_matrix first firstNonNull oneNonzero
  have secondMatrix := Rotation.toTernary_halfTurn_matrix second secondNonNull oneNonzero
  change halfTurn first firstNonNull = form.halfTurn first firstFormNonNull at firstMatrix
  change halfTurn second secondNonNull = form.halfTurn second secondFormNonNull at secondMatrix
  constructor
  · intro equal
    exact (form.halfTurn_eq_iff_same_line first second firstFormNonNull secondFormNonNull twoNonzero).mp
      (firstMatrix.symm.trans (equal.trans secondMatrix))
  · intro sameLine
    exact firstMatrix.trans
      (((form.halfTurn_eq_iff_same_line first second firstFormNonNull secondFormNonNull twoNonzero).mpr
        sameLine).trans secondMatrix.symm)

end Purelib.Geometry.Rotations.Reflection
