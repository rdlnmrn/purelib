module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.Prescribed
public import Purelib.Polynomial.Quadratic.Reciprocal
public import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.LinearAlgebra.Coordinates3.Eigenvector
import Purelib.Geometry.Rotations.Ternary.Cayley.Matrix
import Purelib.Geometry.Rotations.Ternary.Cayley.Anchor
import Purelib.Geometry.Rotations.Ternary.Characteristic
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

/-!
# Arithmetic splitting of Lorentz rotations

The characteristic polynomial of the original Lorentz rotation retains
its fixed-direction factor and a reciprocal quadratic. For a non-null
axis and nonzero half spread different from one, the discriminant has
the square class of the negative original axis quadrance.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Field.SquareClass.Basic
open Purelib.Algebra.Field.Squares
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Rotations.Ternary
open Purelib.Polynomial.Quadratic
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

variable {K : Type*} [ExplicitField K]

/-- The reciprocal quadratic at half spread has the displayed discriminant minus sixteen times the spread product. -/
theorem discriminant_halfSpread (amount : K) :
    Reciprocal.discriminant (1 - 2 * amount) = -16 * amount * (1 - amount) := by
  unfold Reciprocal.discriminant
  ring1

/-- Nonzero half spread different from one gives a nonzero reciprocal discriminant when two is nonzero. -/
theorem discriminant_halfSpread_nonzero (amount : K) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Reciprocal.discriminant (1 - 2 * amount) ≠ 0 := by
  rw [discriminant_halfSpread]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero
      (ExplicitField.neg_ne_zero_of_ne_zero (Characteristic.Nonzero.sixteen_ne_zero twoNonzero)) amountNonzero)
    (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)

variable (oneNonzero : (1 : K) ≠ 0)

/-- The original prescribed-axis rotation has the literal fixed-direction and reciprocal characteristic factors. -/
theorem PrescribedAxisRotation.characteristicValue {axis : Coordinates3.Vector K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount) (twoNonzero : (2 : K) ≠ 0) (point : K) :
    Matrix3.characteristicValue candidate.rotation.matrix point =
      (point - 1) * Reciprocal.eval (1 - 2 * amount) point := by
  rw [Form.characteristicValue_rotation_halfSpread (Form.lorentz oneNonzero)
    candidate.rotation twoNonzero point, candidate.halfSpread_eq]
  rfl

/-- The original prescribed-axis square root gives the square factor from negative axis quadrance to discriminant. -/
@[expose] def PrescribedAxisRotation.discriminantFactor [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : K :=
  4 * (candidate.squareCertificate oneNonzero axisNonNull amountNotOne twoNonzero).root /
    (Form.lorentz oneNonzero).quadrance axis

/-- The retained discriminant square factor is nonzero. -/
theorem PrescribedAxisRotation.discriminantFactor_nonzero [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    candidate.discriminantFactor oneNonzero axisNonNull amountNotOne twoNonzero ≠ 0 :=
  ExplicitField.div_ne_zero (ExplicitField.mul_ne_zero
    (Characteristic.Nonzero.four_ne_zero twoNonzero)
    (candidate.squareCertificate oneNonzero axisNonNull amountNotOne twoNonzero).rootNonzero) axisNonNull

/-- The original reciprocal discriminant is the negative axis quadrance times the square of the retained factor.

The equivalence factor is four times the original axis-square certificate root divided by the original axis quadrance.
The equation retains that exact root and the original quadrance without selecting a new representative. -/
theorem PrescribedAxisRotation.discriminant_eq_factor [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Reciprocal.discriminant (1 - 2 * amount) =
      candidate.discriminantFactor oneNonzero axisNonNull amountNotOne twoNonzero ^ 2 *
        (-(Form.lorentz oneNonzero).quadrance axis) := by
  let quadrance := (Form.lorentz oneNonzero).quadrance axis
  let certificate := candidate.squareCertificate oneNonzero axisNonNull amountNotOne twoNonzero
  have square : certificate.root ^ 2 = quadrance * amount * (1 - amount) := certificate.square
  have cancel := ExplicitField.mul_inv_cancel quadrance axisNonNull
  change Reciprocal.discriminant (1 - 2 * amount) = (4 * certificate.root / quadrance) ^ 2 * (-quadrance)
  symm
  rw [ExplicitField.div_eq_mul_inv]
  calc
    _ = -16 * (certificate.root ^ 2 * quadrance⁻¹) * (quadrance * quadrance⁻¹) := by ring1
    _ = -16 * (certificate.root ^ 2 * quadrance⁻¹) := by rw [cancel, mul_one]
    _ = -16 * ((quadrance * amount * (1 - amount)) * quadrance⁻¹) := by rw [square]
    _ = -16 * amount * (1 - amount) * (quadrance * quadrance⁻¹) := by ring1
    _ = -16 * amount * (1 - amount) := by rw [cancel, mul_one]
    _ = Reciprocal.discriminant (1 - 2 * amount) := (discriminant_halfSpread amount).symm

/-- The reciprocal discriminant of a prescribed-axis Lorentz rotation has the negative original axis square class. -/
theorem PrescribedAxisRotation.discriminant_squareClass [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    SquareClassRepresentative.Equivalent
      (⟨-(Form.lorentz oneNonzero).quadrance axis, ExplicitField.neg_ne_zero_of_ne_zero axisNonNull⟩ :
        SquareClassRepresentative K)
      ⟨Reciprocal.discriminant (1 - 2 * amount),
        discriminant_halfSpread_nonzero amount amountNonzero amountNotOne twoNonzero⟩ :=
  ⟨candidate.discriminantFactor oneNonzero axisNonNull amountNotOne twoNonzero,
    candidate.discriminantFactor_nonzero oneNonzero axisNonNull amountNotOne twoNonzero,
    candidate.discriminant_eq_factor oneNonzero axisNonNull amountNotOne twoNonzero⟩

/-- The original negative-axis square root computes a retained nonzero discriminant square certificate.

Its root is the same supplied axis root multiplied by the original prescribed-axis discriminant factor. -/
@[expose] def PrescribedAxisRotation.discriminantSquareCertificate [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (axisSquare : Witness.NonzeroSquare (-(Form.lorentz oneNonzero).quadrance axis)) :
    Witness.NonzeroSquare (Reciprocal.discriminant (1 - 2 * amount)) := by
  let factor := candidate.discriminantFactor oneNonzero axisNonNull amountNotOne twoNonzero
  refine ⟨factor * axisSquare.root,
    ExplicitField.mul_ne_zero
      (candidate.discriminantFactor_nonzero oneNonzero axisNonNull amountNotOne twoNonzero) axisSquare.rootNonzero, ?_⟩
  calc
    _ = factor ^ 2 * axisSquare.root ^ 2 := by ring1
    _ = factor ^ 2 * (-(Form.lorentz oneNonzero).quadrance axis) :=
      congrArg (fun value => factor ^ 2 * value) axisSquare.square
    _ = Reciprocal.discriminant (1 - 2 * amount) :=
      (candidate.discriminant_eq_factor oneNonzero axisNonNull amountNotOne twoNonzero).symm

/-- The nontrivial characteristic factor of the original Lorentz rotation has a field root exactly when its negative
axis quadrance is a square.

The original axis-square certificate transports square roots to the discriminant, and the reciprocal quadratic gives
the field root with explicit division by the original nonzero two. -/
theorem PrescribedAxisRotation.reciprocal_root_iff [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ point : K, Reciprocal.eval (1 - 2 * amount) point = 0) ↔
      ∃ root : K, root ^ 2 = -(Form.lorentz oneNonzero).quadrance axis := by
  have equivalent := candidate.discriminant_squareClass oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero
  have squareIff := SquareClassRepresentative.square_iff_of_equivalent equivalent
  exact (Reciprocal.exists_root_iff_discriminant_square _ twoNonzero).trans squareIff.symm

/-- A supplied discriminant square certificate factors the actual Lorentz characteristic polynomial into three linear
factors.

The two computed reciprocal roots are distinct, and the third factor is the retained fixed-direction root one. -/
theorem PrescribedAxisRotation.characteristicValue_split {axis : Coordinates3.Vector K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (certificate : Witness.NonzeroSquare (Reciprocal.discriminant (1 - 2 * amount)))
    (twoNonzero : (2 : K) ≠ 0) (point : K) :
    Matrix3.characteristicValue candidate.rotation.matrix point =
      (point - 1) * (point - Reciprocal.positiveRoot (1 - 2 * amount) certificate) *
        (point - Reciprocal.negativeRoot (1 - 2 * amount) certificate) := by
  rw [candidate.characteristicValue oneNonzero twoNonzero point,
    Reciprocal.eval_factor_roots _ certificate twoNonzero point]
  ring1

/-- A root of the reciprocal factor is different from one when the half spread is nonzero. -/
theorem reciprocal_root_ne_one (amount point : K) (amountNonzero : amount ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (root : Reciprocal.eval (1 - 2 * amount) point = 0) : point ≠ 1 := by
  intro equal
  have productZero : 4 * amount = 0 := by
    calc
      _ = Reciprocal.eval (1 - 2 * amount) 1 := by unfold Reciprocal.eval; ring1
      _ = 0 := (congrArg (Reciprocal.eval (1 - 2 * amount)) equal.symm).trans root
  exact (ExplicitField.mul_ne_zero (Characteristic.Nonzero.four_ne_zero twoNonzero) amountNonzero) productZero

/-- Every reciprocal root is a simple characteristic root of the original prescribed-axis rotation.

The nonzero discriminant excludes the center, while the nonzero half spread excludes the fixed-direction root one.
Their product with two is the original characteristic derivative. -/
theorem PrescribedAxisRotation.reciprocal_root_simple {axis : Coordinates3.Vector K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount) (point : K)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (root : Reciprocal.eval (1 - 2 * amount) point = 0) :
    Matrix3.characteristicSlope candidate.rotation.matrix point ≠ 0 := by
  have pointNotOne := reciprocal_root_ne_one amount point amountNonzero twoNonzero root
  have pointNotCenter : point - (1 - 2 * amount) ≠ 0 := by
    intro centeredZero
    have square := Reciprocal.centered_square_of_root (1 - 2 * amount) point root
    apply discriminant_halfSpread_nonzero amount amountNonzero amountNotOne twoNonzero
    calc
      _ = 4 * ((1 - 2 * amount) ^ 2 - 1) := by unfold Reciprocal.discriminant; ring1
      _ = 4 * (point - (1 - 2 * amount)) ^ 2 := congrArg (fun value => 4 * value) square.symm
      _ = 0 := by rw [centeredZero]; ring1
  have traceEquation := candidate.rotation.four_mul_halfSpread twoNonzero
  rw [candidate.halfSpread_eq] at traceEquation
  have traceEqual : Matrix3.trace candidate.rotation.matrix = 3 - 4 * amount := by
    calc
      _ = 3 - (3 - Matrix3.trace candidate.rotation.matrix) := by ring1
      _ = 3 - 4 * amount := congrArg (fun value => 3 - value) traceEquation.symm
  have derivative : Matrix3.characteristicSlope candidate.rotation.matrix point =
      (point - 1) * 2 * (point - (1 - 2 * amount)) := by
    unfold Matrix3.characteristicSlope
    rw [candidate.rotation.principalTrace_matrix, traceEqual]
    calc
      _ = Reciprocal.eval (1 - 2 * amount) point +
          (point - 1) * 2 * (point - (1 - 2 * amount)) := by unfold Reciprocal.eval; ring1
      _ = _ := by rw [root, zero_add]
  rw [derivative]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero (ExplicitField.sub_ne_zero_of_ne pointNotOne) twoNonzero) pointNotCenter

/-- Construct an actual nonzero eigenvector of the original Lorentz rotation from a root of its reciprocal factor.

The original characteristic matrix and its cached adjugate provide the row. The nonzero half spread and discriminant
certify that this root is simple, so finite cofactor selection succeeds. -/
@[expose] def PrescribedAxisRotation.eigenvectorOfReciprocalRoot [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (point : K) (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (root : Reciprocal.eval (1 - 2 * amount) point = 0) : Matrix3.RowEigenvector candidate.rotation.matrix point :=
  Matrix3.simpleRootEigenvector candidate.rotation.matrix point
    (by rw [candidate.characteristicValue oneNonzero twoNonzero point, root, mul_zero])
    (candidate.reciprocal_root_simple oneNonzero point amountNonzero amountNotOne twoNonzero root)

/-- A nontrivial field eigenvalue of the original prescribed-axis Lorentz rotation exists exactly when its negative
axis quadrance is a square.

The converse constructs a nonzero eigenvector from the same reciprocal root. The forward direction factors the
original characteristic value and cancels the supplied nontrivial fixed-direction factor. -/
theorem PrescribedAxisRotation.nontrivial_eigenvalue_iff [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ point : K, point ≠ 1 ∧ Nonempty (Matrix3.RowEigenvector candidate.rotation.matrix point)) ↔
      ∃ root : K, root ^ 2 = -(Form.lorentz oneNonzero).quadrance axis := by
  constructor
  · rintro ⟨point, pointNotOne, ⟨witness⟩⟩
    apply (candidate.reciprocal_root_iff oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero).mp
    refine ⟨point, ?_⟩
    have characteristic := witness.characteristicValue_eq_zero
    rw [candidate.characteristicValue oneNonzero twoNonzero point] at characteristic
    exact ExplicitField.eq_zero_of_mul_eq_zero_left (ExplicitField.sub_ne_zero_of_ne pointNotOne) characteristic
  · intro square
    obtain ⟨point, root⟩ :=
      (candidate.reciprocal_root_iff oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero).mpr square
    exact ⟨point, reciprocal_root_ne_one amount point amountNonzero twoNonzero root,
      ⟨candidate.eigenvectorOfReciprocalRoot oneNonzero point amountNonzero amountNotOne twoNonzero root⟩⟩

/-- Construct the two actual eigenvectors from the same retained negative-axis square root.

The result retains one discriminant certificate. Both original matrix eigenvectors are indexed by the two reciprocal
roots computed from that exact certificate. -/
@[expose] def PrescribedAxisRotation.splitEigenvectors [DecidableEq K]
    {axis : Coordinates3.Vector K} {amount : K} (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (axisSquare : Witness.NonzeroSquare (-(Form.lorentz oneNonzero).quadrance axis)) :
    Σ' certificate : Witness.NonzeroSquare (Reciprocal.discriminant (1 - 2 * amount)),
      Matrix3.RowEigenvector candidate.rotation.matrix (Reciprocal.positiveRoot (1 - 2 * amount) certificate) ×
        Matrix3.RowEigenvector candidate.rotation.matrix (Reciprocal.negativeRoot (1 - 2 * amount) certificate) := by
  let certificate := candidate.discriminantSquareCertificate oneNonzero axisNonNull amountNotOne twoNonzero axisSquare
  have positiveRoot : Reciprocal.eval (1 - 2 * amount) (Reciprocal.positiveRoot (1 - 2 * amount) certificate) = 0 :=
    (Reciprocal.root_iff_eq_roots _ certificate twoNonzero _).mpr (Or.inl rfl)
  have negativeRoot : Reciprocal.eval (1 - 2 * amount) (Reciprocal.negativeRoot (1 - 2 * amount) certificate) = 0 :=
    (Reciprocal.root_iff_eq_roots _ certificate twoNonzero _).mpr (Or.inr rfl)
  exact ⟨certificate,
    candidate.eigenvectorOfReciprocalRoot oneNonzero _ amountNonzero amountNotOne twoNonzero positiveRoot,
    candidate.eigenvectorOfReciprocalRoot oneNonzero _ amountNonzero amountNotOne twoNonzero negativeRoot⟩

/-- An original Lorentz rotation with the supplied complete non-null fixed line has nontrivial field eigenvalues
exactly when the negative axis quadrance is a square.

Its original computed anchor supplies the nonzero scale into the supplied axis. The criterion then constructs actual
nonzero eigenvectors of that same rotation matrix. -/
theorem arithmetic_splitting [DecidableEq K] (axis : Coordinates3.Vector K) (amount : K)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (halfSpread : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = amount)
    (fixedLine : ∀ vector : Coordinates3.Vector K, Matrix3.rowMul vector rotation.matrix = vector ↔
      ∃ factor : K, vector = Coordinates3.Vector.scale factor axis) :
    (∃ point : K, point ≠ 1 ∧ Nonempty (Matrix3.RowEigenvector rotation.matrix point)) ↔
      ∃ root : K, root ^ 2 = -(Form.lorentz oneNonzero).quadrance axis := by
  have notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1 := by
    intro equal
    exact amountNotOne (halfSpread.symm.trans equal)
  let anchorDefined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
  let recovered := rotationAnchorVector oneNonzero rotation anchorDefined
  have recoveredFixed : Matrix3.rowMul recovered rotation.matrix = recovered :=
    rowMul_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn
  obtain ⟨factor, recoveredEqual⟩ := (fixedLine recovered).mp recoveredFixed
  have recoveredNonNull : (Form.lorentz oneNonzero).quadrance recovered ≠ 0 := by
    rw [quadrance_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn, halfSpread]
    exact ExplicitField.div_ne_zero amountNonzero (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)
  have factorNonzero : factor ≠ 0 := by
    intro zero
    rw [recoveredEqual, zero, Coordinates3.Vector.zero_scale, Form.quadrance_zero] at recoveredNonNull
    exact recoveredNonNull rfl
  let candidate : PrescribedAxisRotation oneNonzero axis amount :=
    ⟨rotation, notHalfTurn, halfSpread, anchorDefined, factor, factorNonzero, recoveredEqual⟩
  exact candidate.nontrivial_eigenvalue_iff oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero

end Purelib.Geometry.Rotations.Ternary.Lorentz
