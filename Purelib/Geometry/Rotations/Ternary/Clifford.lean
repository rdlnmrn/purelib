module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Geometry.Quadratic.Ternary.Frame
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Geometry.Rotations.Ternary.Basic
public import Purelib.Geometry.Rotations.Ternary.Reflection
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Quadratic.Ternary.Reflection
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Explicit even Clifford algebra of a ternary form

The four coordinates are stored as one scalar and one displayed vector.  The
product uses the cached adjugate of the form matrix, so it is polynomial in
the supplied finite data and performs no fresh matrix inversion.
-/

namespace Purelib

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section TernaryForm
section NonNullEvenClifford

/-- The normalized Clifford action packaged with an executable inverse and the full form-matrix preservation
certificate. -/
def Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionIsometry {form :
  Ternary.Basic.TernaryForm K}
    (value : form.NonNullEvenClifford) : form.Isometry where
  matrix := (NonNullEvenClifford.actionMatrix value)
  inverseMatrix := (NonNullEvenClifford.actionInverseMatrix value)
  matrix_mul_inverse := (NonNullEvenClifford.actionMatrix_mul_actionInverseMatrix value)
  inverse_mul_matrix := (NonNullEvenClifford.actionInverseMatrix_mul_actionMatrix value)
  preservesMatrix := (NonNullEvenClifford.actionMatrix_preservesMatrix value)

/-- The normalized Clifford action packaged as an executable member of the special orthogonal group of the ternary form.
-/
def Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation {form :
  Ternary.Basic.TernaryForm K}
    (value : form.NonNullEvenClifford) : form.SpecialOrthogonal where
  toIsometry := (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionIsometry value)
  determinantOne := (NonNullEvenClifford.determinant_actionMatrix value)

/-- The bundled isometry acts by the original normalized Clifford action. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionIsometry_act {form :
  Ternary.Basic.TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Coordinates3.Vector K) :
    (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act (NonNullEvenClifford.actionIsometry value)) vector =
        (NonNullEvenClifford.action value) vector := by
  unfold NonNullEvenClifford.actionIsometry Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
  exact (NonNullEvenClifford.rowMul_actionMatrix value) vector

/-- The bundled rotation acts by the original normalized Clifford action. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_act {form :
  Ternary.Basic.TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Coordinates3.Vector K) :
    (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation value).toIsometry)
      vector = (NonNullEvenClifford.action value) vector := by
  change (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionIsometry value)) vector =
    (NonNullEvenClifford.action value) vector
  exact (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionIsometry_act value) vector

/-- The inverse of a product of nonzero scalars is the product of their inverses. -/
private theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.inverse_product {left
  right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  have leftCancel := Algebra.Field.ExplicitField.mul_inv_cancel left leftNonzero
  have rightCancel := Algebra.Field.ExplicitField.mul_inv_cancel right rightNonzero
  have productNonzero :=
    Algebra.Field.ExplicitField.mul_ne_zero leftNonzero rightNonzero
  have productCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (left * right) productNonzero
  calc
    (left * right)⁻¹ = (left * right)⁻¹ * 1 := by rw [mul_one]
    _ = (left * right)⁻¹ *
        ((left * right) * (left⁻¹ * right⁻¹)) := by
      rw [show (left * right) * (left⁻¹ * right⁻¹) = 1 by
        calc
          (left * right) * (left⁻¹ * right⁻¹) =
              (left * left⁻¹) * (right * right⁻¹) := by ring1
          _ = 1 := by rw [leftCancel, rightCancel, one_mul]]
    _ = ((left * right) * (left * right)⁻¹) *
        (left⁻¹ * right⁻¹) := by ring1
    _ = left⁻¹ * right⁻¹ := by rw [productCancel, one_mul]

/-- A non-null vector, embedded as a pure even Clifford representative. Its normalized action is the form-relative half
turn about that vector. -/
def Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue (form :
  Ternary.Basic.TernaryForm K) (axis : Coordinates3.Vector K)
    (nonNull : form.quadrance axis ≠ 0) : form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.ofVector form axis
  normNonzero := by
    have productNonzero := Algebra.Field.ExplicitField.mul_ne_zero
      form.determinantNonzero nonNull
    intro normZero
    apply productNonzero
    calc
      form.determinant * form.quadrance axis =
          (0 : K) ^ 2 + form.determinant * form.quadrance axis := by ring1
      _ = 0 := normZero

/-- The pure-axis Clifford value has norm equal to the form determinant times the axis quadrance. -/
@[simp] theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_norm (form :
  Ternary.Basic.TernaryForm K)
    (axis : Coordinates3.Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (EvenClifford.norm (NonNullEvenClifford.halfTurnValue form axis nonNull).toEvenClifford) =
      form.determinant * form.quadrance axis := by
  unfold NonNullEvenClifford.halfTurnValue EvenClifford.ofVector EvenClifford.norm
  ring1

/-- The pure-vector Clifford sandwich is exactly the displayed half-turn action, with the determinant factors cancelled
constructively. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_action (form :
  Ternary.Basic.TernaryForm K) (axis : Coordinates3.Vector K)
    (nonNull : form.quadrance axis ≠ 0) (vector : Coordinates3.Vector K) :
    (NonNullEvenClifford.action (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form axis
      nonNull)) vector =
      Matrix3.rowMul vector (form.halfTurn axis nonNull) := by
  have determinantCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    form.determinant form.determinantNonzero
  have reverseDeterminantCancel :
      form.determinant⁻¹ * form.determinant = (1 : K) := by
    calc
      form.determinant⁻¹ * form.determinant =
          form.determinant * form.determinant⁻¹ := by ring1
      _ = 1 := determinantCancel
  have quadranceCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (form.quadrance axis) nonNull
  have reverseQuadranceCancel :
      (form.quadrance axis)⁻¹ * form.quadrance axis = (1 : K) := by
    calc
      (form.quadrance axis)⁻¹ * form.quadrance axis =
          form.quadrance axis * (form.quadrance axis)⁻¹ := by ring1
      _ = 1 := quadranceCancel
  have vectorCoefficient :
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (-form.determinant * form.quadrance axis) = (-1 : K) := by
    calc
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (-form.determinant * form.quadrance axis) =
        -(form.determinant⁻¹ * form.determinant) *
          ((form.quadrance axis)⁻¹ * form.quadrance axis) := by ring1
      _ = -1 := by
        rw [reverseDeterminantCancel, reverseQuadranceCancel]
        ring1
  have axisCoefficient :
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (2 * form.determinant * form.bilinear vector axis) =
        2 * form.bilinear vector axis * (form.quadrance axis)⁻¹ := by
    calc
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (2 * form.determinant * form.bilinear vector axis) =
        (form.determinant⁻¹ * form.determinant) *
          (2 * form.bilinear vector axis * (form.quadrance axis)⁻¹) := by ring1
      _ = 2 * form.bilinear vector axis * (form.quadrance axis)⁻¹ := by
        rw [reverseDeterminantCancel, one_mul]
  unfold NonNullEvenClifford.action
  rw [Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_norm]
  change Coordinates3.Vector.scale (form.determinant * form.quadrance axis)⁻¹
      (EvenClifford.actionNumerator (EvenClifford.ofVector form axis) vector) =
    Matrix3.rowMul vector (form.halfTurn axis nonNull)
  unfold EvenClifford.actionNumerator EvenClifford.ofVector
    TernaryForm.halfTurn
  rw [Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.inverse_product form.determinantNonzero nonNull,
    Matrix3.rowMul_neg, form.rowMul_reflection]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [show (0 : K) ^ 2 - form.determinant * form.quadrance axis =
      -form.determinant * form.quadrance axis by ring1,
    show (-2 : K) * 0 = 0 by ring1]
  change Coordinates3.Vector.scale (form.determinant⁻¹ * (form.quadrance axis)⁻¹)
      (Coordinates3.Vector.add
        (Coordinates3.Vector.add
          (Coordinates3.Vector.scale (-form.determinant * form.quadrance axis) vector)
          (Coordinates3.Vector.scale
            (2 * form.determinant * form.bilinear vector axis) axis))
        (Coordinates3.Vector.scale 0 (form.cliffordCross vector axis))) =
    Coordinates3.Vector.neg
      (Coordinates3.Vector.sub vector
        (Coordinates3.Vector.scale
          (2 * form.bilinear vector axis * (form.quadrance axis)⁻¹) axis))
  rw [Coordinates3.Vector.zero_scale, Coordinates3.Vector.add_zero, Coordinates3.Vector.scale_add,
    Coordinates3.Vector.scale_scale, Coordinates3.Vector.scale_scale,
    vectorCoefficient, axisCoefficient]
  ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.sub Coordinates3.Vector.scale Coordinates3.Vector.neg <;>
    ring1

/-- The pure-axis Clifford value acts by the form-relative half-turn matrix. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_actionMatrix (form :
  Ternary.Basic.TernaryForm K)
    (axis : Coordinates3.Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (NonNullEvenClifford.actionMatrix (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form
      axis nonNull)) =
      form.halfTurn axis nonNull := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [NonNullEvenClifford.rowMul_actionMatrix,
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_action]

/-- The Clifford action contains every displayed form-relative half turn. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_actionRotation (form
  : Ternary.Basic.TernaryForm K)
    (axis : Coordinates3.Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form axis nonNull)) =
      form.halfTurnRotation axis nonNull := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_actionMatrix form axis nonNull

/-- The normalized Clifford action is multiplicative. With displayed row vectors, the left representative acts first and
the right one second. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_mul {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.NonNullEvenClifford) (vector : Coordinates3.Vector K) :
    (NonNullEvenClifford.action (NonNullEvenClifford.mul left right)) vector =
      (NonNullEvenClifford.action right) ((NonNullEvenClifford.action left) vector) := by
  unfold NonNullEvenClifford.action
  change
    Coordinates3.Vector.scale
        (EvenClifford.norm
          (EvenClifford.mul left.toEvenClifford right.toEvenClifford))⁻¹
        (EvenClifford.actionNumerator
          (EvenClifford.mul left.toEvenClifford right.toEvenClifford)
          vector) =
      Coordinates3.Vector.scale (EvenClifford.norm right.toEvenClifford)⁻¹
        ((EvenClifford.actionNumerator right.toEvenClifford)
          (Coordinates3.Vector.scale (EvenClifford.norm left.toEvenClifford)⁻¹
            ((EvenClifford.actionNumerator left.toEvenClifford) vector)))
  rw [EvenClifford.norm_mul, EvenClifford.actionNumerator_mul,
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.inverse_product left.normNonzero right.normNonzero,
    EvenClifford.actionNumerator_scale_vector,
    Coordinates3.Vector.scale_scale]
  ext <;> unfold Coordinates3.Vector.scale <;> ring1

/-- Matrix form of multiplicativity of the normalized Clifford action. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_mul {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.NonNullEvenClifford) :
    (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.mul left right)) =
      Matrix3.mul (NonNullEvenClifford.actionMatrix left) (NonNullEvenClifford.actionMatrix right) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [NonNullEvenClifford.rowMul_actionMatrix, ← Matrix3.rowMul_mul,
    NonNullEvenClifford.rowMul_actionMatrix, NonNullEvenClifford.rowMul_actionMatrix,
      Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_mul]

/-- The Clifford action is a homomorphism into the displayed special-orthogonal group. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_mul {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.NonNullEvenClifford) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul left right))
      =
      SpecialOrthogonal.mul (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation left)
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_mul left right

/-- Products of displayed form-relative half turns are computed by multiplying their pure-vector Clifford
representatives. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnRotation_mul (form :
  Ternary.Basic.TernaryForm K)
    (first second : Coordinates3.Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0) :
    SpecialOrthogonal.mul
        (form.halfTurnRotation first firstNonNull)
        (form.halfTurnRotation second secondNonNull) =
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form first firstNonNull)
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form second secondNonNull))) := by
  calc
    SpecialOrthogonal.mul
        (form.halfTurnRotation first firstNonNull)
        (form.halfTurnRotation second secondNonNull) =
      SpecialOrthogonal.mul
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
          (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form first firstNonNull))
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
          (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form second secondNonNull)) :=
          by
          rw [Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_actionRotation,
            Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue_actionRotation]
    _ = (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form first firstNonNull)
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form second secondNonNull))) :=
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_mul _ _).symm

/-- The normalized action is independent of a nonzero homogeneous rescaling of its displayed Clifford representative. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_scale {form :
  Ternary.Basic.TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K) :
    (NonNullEvenClifford.action (NonNullEvenClifford.scale factor factorNonzero value)) vector =
      (NonNullEvenClifford.action value) vector := by
  have squareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have squareCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (factor ^ 2) squareNonzero
  have reverseSquareCancel : (factor ^ 2)⁻¹ * factor ^ 2 = 1 := by
    calc
      (factor ^ 2)⁻¹ * factor ^ 2 =
          factor ^ 2 * (factor ^ 2)⁻¹ := by ring1
      _ = 1 := squareCancel
  unfold NonNullEvenClifford.action NonNullEvenClifford.scale
  rw [EvenClifford.norm_scale,
    EvenClifford.actionNumerator_scale,
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.inverse_product squareNonzero value.normNonzero,
    Coordinates3.Vector.scale_scale]
  congr 1
  calc
    ((factor ^ 2)⁻¹ * (EvenClifford.norm value.toEvenClifford)⁻¹) * factor ^ 2 =
        ((factor ^ 2)⁻¹ * factor ^ 2) *
          (EvenClifford.norm value.toEvenClifford)⁻¹ := by ring1
    _ = (EvenClifford.norm value.toEvenClifford)⁻¹ := by
      rw [reverseSquareCancel, one_mul]

/-- Nonzero homogeneous rescaling leaves the Clifford action matrix unchanged. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_scale {form :
  Ternary.Basic.TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford) :
    (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.scale factor factorNonzero value)) =
      (NonNullEvenClifford.actionMatrix value) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [NonNullEvenClifford.rowMul_actionMatrix, NonNullEvenClifford.rowMul_actionMatrix,
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_scale]

/-- Equivalent Clifford representatives act identically on each displayed vector. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_respects_equivalent {form :
  Ternary.Basic.TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : (NonNullEvenClifford.Equivalent left) right) (vector : Coordinates3.Vector K) :
    (NonNullEvenClifford.action left) vector = (NonNullEvenClifford.action right) vector := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have rightScaled : right = NonNullEvenClifford.scale factor factorNonzero left := by
    apply NonNullEvenClifford.ext
    · exact congrArg EvenClifford.scalar rightValue
    · exact congrArg EvenClifford.vector rightValue
  rw [rightScaled, Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_scale]

/-- Equivalent Clifford representatives have equal action matrices. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_respects_equivalent
  {form : Ternary.Basic.TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : (NonNullEvenClifford.Equivalent left) right) :
    (NonNullEvenClifford.actionMatrix left) = (NonNullEvenClifford.actionMatrix right) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [(NonNullEvenClifford.rowMul_actionMatrix left), (NonNullEvenClifford.rowMul_actionMatrix right)]
  exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_respects_equivalent equivalent vector

/-- The identity Clifford value fixes every vector. -/
@[simp] theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_identity (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) : (NonNullEvenClifford.action (NonNullEvenClifford.identity form)) vector = vector
      := by
  unfold NonNullEvenClifford.action NonNullEvenClifford.identity
  rw [EvenClifford.norm_identity,
    EvenClifford.actionNumerator_identity]
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel (1 : K) form.one_ne_zero
    simpa only [one_mul] using cancel
  rw [oneInverse, Coordinates3.Vector.one_scale]

/-- The identity Clifford value has the identity action matrix. -/
@[simp] theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_identity
  (form : Ternary.Basic.TernaryForm K) :
    (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.identity form)) = Matrix3.identity := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [NonNullEvenClifford.rowMul_actionMatrix,
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.action_identity, Matrix3.rowMul_identity]

/-- The identity Clifford value gives the identity form rotation. -/
@[simp] theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_identity
  (form : Ternary.Basic.TernaryForm K) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.identity form))
      =
      SpecialOrthogonal.identity form := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_identity form

/-- Equivalent projective Clifford representatives determine the same special-orthogonal transformation. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_respects_equivalent
  {form : Ternary.Basic.TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : (NonNullEvenClifford.Equivalent left) right) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation left) =
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_respects_equivalent equivalent

/-- If the normalized action fixes a displayed vector, its denominator-cleared numerator is the reduced norm times that
vector. -/
theorem
  Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionNumerator_eq_scale_norm_of_action_eq
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K) (fixed : (NonNullEvenClifford.action value) vector = vector) :
    (EvenClifford.actionNumerator value.toEvenClifford) vector =
      Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford) vector := by
  have normCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  calc
    (EvenClifford.actionNumerator value.toEvenClifford) vector =
        Coordinates3.Vector.scale 1 ((EvenClifford.actionNumerator value.toEvenClifford) vector) :=
      (Coordinates3.Vector.one_scale _).symm
    _ = Coordinates3.Vector.scale
        ((EvenClifford.norm value.toEvenClifford) * (EvenClifford.norm value.toEvenClifford)⁻¹)
        ((EvenClifford.actionNumerator value.toEvenClifford) vector) := by
      rw [normCancel]
    _ = Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford)
        (Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford)⁻¹
          ((EvenClifford.actionNumerator value.toEvenClifford) vector)) :=
      (Coordinates3.Vector.scale_scale _ _ _).symm
    _ = Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford) ((NonNullEvenClifford.action value) vector)
      := rfl
    _ = Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford) vector := by rw [fixed]

/-- A pure vector fixed by the normalized action commutes with the acting Clifford representative. -/
theorem
  Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.ofVector_mul_eq_mul_ofVector_of_action_eq
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Coordinates3.Vector K) (fixed : (NonNullEvenClifford.action value) vector = vector) :
    EvenClifford.mul (EvenClifford.ofVector form vector)
        value.toEvenClifford =
      EvenClifford.mul value.toEvenClifford
        (EvenClifford.ofVector form vector) := by
  let pure := EvenClifford.ofVector form vector
  have sandwich :
      EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate value.toEvenClifford) pure)
          value.toEvenClifford =
        EvenClifford.scale (EvenClifford.norm value.toEvenClifford) pure := by
    calc
      EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate value.toEvenClifford) pure)
          value.toEvenClifford =
        EvenClifford.ofVector form
          ((EvenClifford.actionNumerator value.toEvenClifford) vector) :=
        EvenClifford.conjugate_mul_ofVector_mul
          value.toEvenClifford vector
      _ = EvenClifford.ofVector form
          (Coordinates3.Vector.scale (EvenClifford.norm value.toEvenClifford) vector) := by
        rw [(Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionNumerator_eq_scale_norm_of_action_eq
          value) vector fixed]
      _ = EvenClifford.scale (EvenClifford.norm value.toEvenClifford) pure := by
        exact EvenClifford.ofVector_scale form
          (EvenClifford.norm value.toEvenClifford) vector
  apply EvenClifford.eq_of_scale_eq_scale
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  calc
    EvenClifford.scale (EvenClifford.norm value.toEvenClifford)
        (EvenClifford.mul pure value.toEvenClifford) =
      EvenClifford.mul
        (EvenClifford.scale (EvenClifford.norm value.toEvenClifford)
          (EvenClifford.identity form))
        (EvenClifford.mul pure value.toEvenClifford) := by
          rw [EvenClifford.mul_scale_left, EvenClifford.identity_mul]
    _ = EvenClifford.mul
        (EvenClifford.mul value.toEvenClifford
          (EvenClifford.conjugate value.toEvenClifford))
        (EvenClifford.mul pure value.toEvenClifford) := by
          rw [EvenClifford.mul_conjugate_eq_scale_identity]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.mul (EvenClifford.conjugate value.toEvenClifford)
          (EvenClifford.mul pure value.toEvenClifford)) := by
          rw [EvenClifford.mul_assoc]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate value.toEvenClifford) pure)
          value.toEvenClifford) := by
          rw [← EvenClifford.mul_assoc
            (EvenClifford.conjugate value.toEvenClifford) pure value.toEvenClifford]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.scale (EvenClifford.norm value.toEvenClifford) pure) := by
          rw [sandwich]
    _ = EvenClifford.scale (EvenClifford.norm value.toEvenClifford)
        (EvenClifford.mul value.toEvenClifford pure) :=
      EvenClifford.mul_scale_right (EvenClifford.norm value.toEvenClifford)
        value.toEvenClifford pure

/-- In characteristic different from two, a displayed vector fixed by the normalized action has zero Clifford cross with
the representative's vector coordinate. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.cliffordCross_eq_zero_of_action_eq
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) (vector : Coordinates3.Vector K)
    (fixed : (NonNullEvenClifford.action value) vector = vector) :
    form.cliffordCross vector value.toEvenClifford.vector = Coordinates3.Vector.zero := by
  have commutes :=
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.ofVector_mul_eq_mul_ofVector_of_action_eq value)
      vector fixed
  have vectorEqual := congrArg EvenClifford.vector commutes
  change EvenClifford.productVector form 0 value.toEvenClifford.scalar
      vector value.toEvenClifford.vector =
    EvenClifford.productVector form value.toEvenClifford.scalar 0
      value.toEvenClifford.vector vector at vectorEqual
  unfold EvenClifford.productVector at vectorEqual
  rw [form.cliffordCross_anticomm value.toEvenClifford.vector vector]
    at vectorEqual
  apply Coordinates3.Vector.ext
  · apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
    have coordinate := congrArg Coordinates3.Vector.t vectorEqual
    unfold Coordinates3.Vector.sub Coordinates3.Vector.add
      Coordinates3.Vector.scale Coordinates3.Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.t +
          value.toEvenClifford.scalar * vector.t) -
        (form.cliffordCross vector value.toEvenClifford.vector).t =
      (value.toEvenClifford.scalar * vector.t +
          0 * value.toEvenClifford.vector.t) -
        -(form.cliffordCross vector value.toEvenClifford.vector).t
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).t =
          ((value.toEvenClifford.scalar * vector.t +
              0 * value.toEvenClifford.vector.t) -
            -(form.cliffordCross vector value.toEvenClifford.vector).t) -
          ((0 * value.toEvenClifford.vector.t +
              value.toEvenClifford.scalar * vector.t) -
            (form.cliffordCross vector value.toEvenClifford.vector).t) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1
  · apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
    have coordinate := congrArg Coordinates3.Vector.r vectorEqual
    unfold Coordinates3.Vector.sub Coordinates3.Vector.add
      Coordinates3.Vector.scale Coordinates3.Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.r +
          value.toEvenClifford.scalar * vector.r) -
        (form.cliffordCross vector value.toEvenClifford.vector).r =
      (value.toEvenClifford.scalar * vector.r +
          0 * value.toEvenClifford.vector.r) -
        -(form.cliffordCross vector value.toEvenClifford.vector).r
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).r =
          ((value.toEvenClifford.scalar * vector.r +
              0 * value.toEvenClifford.vector.r) -
            -(form.cliffordCross vector value.toEvenClifford.vector).r) -
          ((0 * value.toEvenClifford.vector.r +
              value.toEvenClifford.scalar * vector.r) -
            (form.cliffordCross vector value.toEvenClifford.vector).r) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1
  · apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
    have coordinate := congrArg Coordinates3.Vector.s vectorEqual
    unfold Coordinates3.Vector.sub Coordinates3.Vector.add
      Coordinates3.Vector.scale Coordinates3.Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.s +
          value.toEvenClifford.scalar * vector.s) -
        (form.cliffordCross vector value.toEvenClifford.vector).s =
      (value.toEvenClifford.scalar * vector.s +
          0 * value.toEvenClifford.vector.s) -
        -(form.cliffordCross vector value.toEvenClifford.vector).s
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).s =
          ((value.toEvenClifford.scalar * vector.s +
              0 * value.toEvenClifford.vector.s) -
            -(form.cliffordCross vector value.toEvenClifford.vector).s) -
          ((0 * value.toEvenClifford.vector.s +
              value.toEvenClifford.scalar * vector.s) -
            (form.cliffordCross vector value.toEvenClifford.vector).s) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1

/-- A trivial normalized action has zero vector coordinate. This is the finite coordinate heart of the projective
Clifford kernel calculation. -/
theorem
  Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.vector_eq_zero_of_actionMatrix_eq_identity
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0)
    (trivial : (NonNullEvenClifford.actionMatrix value) = Matrix3.identity) :
    value.toEvenClifford.vector = Coordinates3.Vector.zero := by
  apply form.eq_zero_of_cliffordCross_right_eq_zero
  intro vector
  apply (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.cliffordCross_eq_zero_of_action_eq value)
    twoNonzero
  calc
    (NonNullEvenClifford.action value) vector = Matrix3.rowMul vector (NonNullEvenClifford.actionMatrix value) :=
      ((NonNullEvenClifford.rowMul_actionMatrix value) vector).symm
    _ = Matrix3.rowMul vector Matrix3.identity := by rw [trivial]
    _ = vector := Matrix3.rowMul_identity vector

/-- A nonzero-norm Clifford representative is projectively scalar exactly when its displayed vector coordinate vanishes.
-/
theorem
  Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.equivalent_identity_iff_vector_eq_zero
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford) :
    (NonNullEvenClifford.Equivalent (NonNullEvenClifford.identity form)) value ↔
      value.toEvenClifford.vector = Coordinates3.Vector.zero := by
  constructor
  · intro equivalent
    rcases equivalent with ⟨factor, _factorNonzero, rawEqual⟩
    have vectorEqual := congrArg EvenClifford.vector rawEqual
    change value.toEvenClifford.vector =
      Coordinates3.Vector.scale factor Coordinates3.Vector.zero at vectorEqual
    rw [Coordinates3.Vector.scale_zero] at vectorEqual
    exact vectorEqual
  · intro vectorZero
    have scalarNonzero : value.toEvenClifford.scalar ≠ 0 := by
      intro scalarZero
      apply value.normNonzero
      unfold EvenClifford.norm
      rw [vectorZero, form.quadrance_zero, scalarZero]
      ring1
    refine ⟨value.toEvenClifford.scalar, scalarNonzero, ?_⟩
    apply EvenClifford.ext
    · change value.toEvenClifford.scalar =
        value.toEvenClifford.scalar * 1
      ring1
    · change value.toEvenClifford.vector =
        Coordinates3.Vector.scale value.toEvenClifford.scalar Coordinates3.Vector.zero
      rw [vectorZero, Coordinates3.Vector.scale_zero]

/-- Exact kernel of the projective Clifford action: in characteristic different from two, the identity rotation is
represented precisely by the nonzero scalar Clifford points. -/
theorem
  Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_eq_identity_iff_equivalent_identity
    {form : Ternary.Basic.TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation value) = SpecialOrthogonal.identity
      form ↔
      (NonNullEvenClifford.Equivalent (NonNullEvenClifford.identity form)) value := by
  constructor
  · intro rotationEqual
    have matrixEqual := congrArg
      (fun rotation : form.SpecialOrthogonal => rotation.matrix)
      rotationEqual
    change (NonNullEvenClifford.actionMatrix value) = Matrix3.identity at matrixEqual
    apply (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.equivalent_identity_iff_vector_eq_zero
      value).2
    exact (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.vector_eq_zero_of_actionMatrix_eq_identity
      value)
      twoNonzero matrixEqual
  · intro equivalent
    calc
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation value) =
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.identity
        form)) :=
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_respects_equivalent
          equivalent).symm
      _ = SpecialOrthogonal.identity form :=
        Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_identity form

/-- Clifford conjugation maps to inversion in the displayed special-orthogonal group. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_conjugate {form :
  Ternary.Basic.TernaryForm K}
    (value : form.NonNullEvenClifford) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.conjugate
      value)) =
      SpecialOrthogonal.inverse (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation value) :=
        by
  apply SpecialOrthogonal.eq_of_matrix_eq
  change (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value)) =
    (NonNullEvenClifford.actionInverseMatrix value)
  have conjugateProduct :
      Matrix3.mul (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value))
        (NonNullEvenClifford.actionMatrix value) =
        Matrix3.identity := by
    calc
      Matrix3.mul (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value))
        (NonNullEvenClifford.actionMatrix value) =
          (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.mul (NonNullEvenClifford.conjugate value) value)) :=
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_mul (NonNullEvenClifford.conjugate
          value) value).symm
      _ = (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.identity form)) :=
        Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_respects_equivalent
          (NonNullEvenClifford.conjugate_mul_equivalent_identity value)
      _ = Matrix3.identity := Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionMatrix_identity form
  calc
    (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value)) =
        Matrix3.mul (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value)) Matrix3.identity :=
      (Matrix3.mul_identity (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value))).symm
    _ = Matrix3.mul (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value))
        (Matrix3.mul (NonNullEvenClifford.actionMatrix value) (NonNullEvenClifford.actionInverseMatrix value)) := by
      rw [(NonNullEvenClifford.actionMatrix_mul_actionInverseMatrix value)]
    _ = Matrix3.mul
        (Matrix3.mul (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value))
          (NonNullEvenClifford.actionMatrix value))
        (NonNullEvenClifford.actionInverseMatrix value) := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul Matrix3.identity (NonNullEvenClifford.actionInverseMatrix value) := by
      rw [conjugateProduct]
    _ = (NonNullEvenClifford.actionInverseMatrix value) :=
      Matrix3.identity_mul (NonNullEvenClifford.actionInverseMatrix value)

/-- Projective faithfulness of the Clifford action. Equality of the displayed special-orthogonal transformations is
exactly equality up to an explicit nonzero homogeneous scale. -/
theorem Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_eq_iff_equivalent
    {form : Ternary.Basic.TernaryForm K} (left right : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation left) =
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) ↔
      (NonNullEvenClifford.Equivalent left) right := by
  constructor
  · intro actionEqual
    have relativeAction :
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate left) right)) =
          SpecialOrthogonal.identity form := by
      calc
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate left) right)) =
            SpecialOrthogonal.mul
              (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
                (NonNullEvenClifford.conjugate left))
                (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) :=
          Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_mul
            (NonNullEvenClifford.conjugate left) right
        _ = SpecialOrthogonal.mul
              (SpecialOrthogonal.inverse (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
                left))
              (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) := by
          rw [Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_conjugate]
        _ = SpecialOrthogonal.mul
              (SpecialOrthogonal.inverse (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
                left))
              (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation left) := by rw [←
                actionEqual]
        _ = SpecialOrthogonal.identity form :=
          SpecialOrthogonal.inverse_mul (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
            left)
    have relativeIdentity :
        (NonNullEvenClifford.Equivalent (NonNullEvenClifford.identity form)) (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate left) right) :=
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_eq_identity_iff_equivalent_identity
        (NonNullEvenClifford.mul (NonNullEvenClifford.conjugate left) right) twoNonzero).1 relativeAction
    have leftToRelative :
        (NonNullEvenClifford.Equivalent left) (NonNullEvenClifford.mul left (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate left) right)) := by
      have productEquivalent := NonNullEvenClifford.mul_respects_equivalent
        (NonNullEvenClifford.equivalent_refl left) relativeIdentity
      simpa only [NonNullEvenClifford.mul_identity] using productEquivalent
    have relativeToRight :
        (NonNullEvenClifford.Equivalent (NonNullEvenClifford.mul left (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate left) right))) right := by
      have productEquivalent := NonNullEvenClifford.mul_respects_equivalent
        (NonNullEvenClifford.mul_conjugate_equivalent_identity left) (NonNullEvenClifford.equivalent_refl right)
      simpa only [NonNullEvenClifford.mul_assoc, NonNullEvenClifford.identity_mul] using productEquivalent
    exact NonNullEvenClifford.equivalent_trans leftToRelative relativeToRight
  · intro equivalent
    exact Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_respects_equivalent equivalent

end NonNullEvenClifford

/-- The displayed linear displacement operator \(R-I\). -/
def Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacementMatrix {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) : Coordinates3.Matrix3 K :=
  Matrix3.sub rotation.matrix Matrix3.identity

/-- The displacement of a displayed vector under a form rotation. -/
def Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) (vector : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) vector) vector

/-- Row multiplication by `R-I` computes the displacement under the rotation. -/
theorem Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.rowMul_displacementMatrix
    {form : Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Coordinates3.Vector K) :
    Matrix3.rowMul vector (SpecialOrthogonal.displacementMatrix rotation) =
      (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) vector := by
  unfold SpecialOrthogonal.displacementMatrix
    Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
        Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
  rw [Matrix3.rowMul_sub, Matrix3.rowMul_identity]

/-- The rotation displacement operator preserves vector addition. -/
theorem Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_add
    {form : Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal)
    (left right : Coordinates3.Vector K) :
    (SpecialOrthogonal.displacement rotation) (Coordinates3.Vector.add left right) =
      Coordinates3.Vector.add ((SpecialOrthogonal.displacement rotation) left)
        ((SpecialOrthogonal.displacement rotation) right) := by
  ext <;> unfold SpecialOrthogonal.displacement Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
    Coordinates3.Vector.add Coordinates3.Vector.sub Matrix3.rowMul <;> ring1

/-- The rotation displacement operator preserves vector subtraction. -/
theorem Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_sub
    {form : Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal)
    (left right : Coordinates3.Vector K) :
    (SpecialOrthogonal.displacement rotation) (Coordinates3.Vector.sub left right) =
      Coordinates3.Vector.sub ((SpecialOrthogonal.displacement rotation) left)
        ((SpecialOrthogonal.displacement rotation) right) := by
  ext <;> unfold SpecialOrthogonal.displacement Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
    Coordinates3.Vector.sub Matrix3.rowMul <;> ring1

/-- The displacement operator commutes with the rotation that defines it. -/
theorem Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_act
    {form : Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Coordinates3.Vector K) :
    (SpecialOrthogonal.displacement rotation) ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
        rotation.toIsometry) vector) =
      (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) ((SpecialOrthogonal.displacement
          rotation) vector) := by
  ext <;> unfold SpecialOrthogonal.displacement Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
    Coordinates3.Vector.sub Matrix3.rowMul <;> ring1

/-- Coordinate expansion of the displacement operator. -/
theorem Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_coordinateExpansion
    {form : Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Coordinates3.Vector K) :
    (SpecialOrthogonal.displacement rotation) vector =
      Coordinates3.Vector.add
        (Coordinates3.Vector.add
          (Coordinates3.Vector.scale vector.t
            ((SpecialOrthogonal.displacement rotation) (⟨1, 0, 0⟩ : Coordinates3.Vector K)))
          (Coordinates3.Vector.scale vector.r
            ((SpecialOrthogonal.displacement rotation) (⟨0, 1, 0⟩ : Coordinates3.Vector K))))
        (Coordinates3.Vector.scale vector.s
          ((SpecialOrthogonal.displacement rotation) (⟨0, 0, 1⟩ : Coordinates3.Vector K))) := by
  ext <;> unfold SpecialOrthogonal.displacement Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
    Coordinates3.Vector.add Coordinates3.Vector.sub Coordinates3.Vector.scale Matrix3.rowMul <;> ring1

set_option genInjectivity false in
/-- A cached non-null seed whose displacement under a displayed rotation is also non-null.

The seed is the original displayed vector, and both nonzero-quadrance witnesses refer to that same seed and its actual
displacement. -/
structure Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullDisplacementWitness (form :
  Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  /-- The cached non-null seed vector. -/ seed : Coordinates3.Vector K
  /-- The retained seed has nonzero form quadrance. -/ seedNonNull : form.quadrance seed ≠ 0
  /-- The displacement of the original seed has nonzero form quadrance. -/ displacementNonNull : form.quadrance
    ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) seed) ≠ 0

constructive_injectivity Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullDisplacementWitness

/-- Convert a vector with non-null displacement into a non-null seed with non-null displacement.

A non-null input is retained directly. For a null input, the original sum and
difference with its image are tested in their original order; the parallelogram
identity certifies the selected seed and its cached displacement. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (rotation : form.SpecialOrthogonal)
    (vector : Coordinates3.Vector K)
    (displacementNonNull :
      form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) vector) ≠
        0)
    (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullDisplacementWitness form rotation := by
  by_cases vectorNull : form.quadrance vector = 0
  · let moved := (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) vector
    let sum := Coordinates3.Vector.add vector moved
    let difference := Coordinates3.Vector.sub vector moved
    have movedNull : form.quadrance moved = 0 := by
      unfold moved
      rw [(SpecialOrthogonal.quadrance_act rotation), vectorNull]
    have sumQuadrance :
        form.quadrance sum =
          -form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
            vector) := by
      have addition := form.quadrance_add vector moved
      have subtraction := form.quadrance_sub moved vector
      change form.quadrance sum = _ at addition
      change form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
        vector) = _
        at subtraction
      rw [vectorNull, movedNull] at addition subtraction
      calc
        form.quadrance sum =
            0 + 2 * form.bilinear vector moved + 0 := addition
        _ = -(0 - 2 * form.bilinear moved vector + 0) := by
          rw [form.bilinear_comm moved vector]
          ring1
        _ = -form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
          vector) := by
          rw [subtraction]
    have differenceQuadrance :
        form.quadrance difference =
          form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) vector)
            := by
      have first := form.quadrance_sub vector moved
      have second := form.quadrance_sub moved vector
      change form.quadrance difference = _ at first
      change form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
        vector) = _ at second
      rw [vectorNull, movedNull] at first second
      calc
        form.quadrance difference =
            0 - 2 * form.bilinear vector moved + 0 := first
        _ = 0 - 2 * form.bilinear moved vector + 0 := by
          rw [form.bilinear_comm vector moved]
        _ = form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
          vector) := second.symm
    have sumNonNull : form.quadrance sum ≠ 0 := by
      intro sumZero
      apply displacementNonNull
      have negZero :
          -form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
            vector) = 0 := by
        rewrite [← sumQuadrance, sumZero]
        exact Eq.refl _
      have cancel := AddGroup.neg_add_cancel
        (form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) vector))
      rewrite [negZero, zero_add] at cancel
      exact cancel
    have differenceNonNull : form.quadrance difference ≠ 0 := by
      rw [differenceQuadrance]
      exact displacementNonNull
    have movedDisplacementQuadrance :
        form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) moved) =
          form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) vector)
            := by
      unfold moved
      rw [(Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_act rotation),
        (SpecialOrthogonal.quadrance_act rotation)]
    have displacementParallelogram :
        form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) sum) +
            form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
              difference) =
          4 * form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
            vector) := by
      rw [(Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_add rotation),
        (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_sub rotation),
        form.quadrance_add, form.quadrance_sub,
        movedDisplacementQuadrance]
      ring1
    by_cases sumDisplacementZero :
        form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) sum) = 0
    · refine ⟨difference, differenceNonNull, ?_⟩
      intro differenceDisplacementZero
      have fourTimesZero :
          (2 * 2) * form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
            rotation) vector) = 0 := by
        calc
          (2 * 2) * form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
            rotation) vector) =
              4 * form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                vector) := by
            ring1
          _ = form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
            sum) +
                form.quadrance ((Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                  difference) :=
            displacementParallelogram.symm
          _ = 0 := by
            rw [sumDisplacementZero, differenceDisplacementZero]
            ring1
      have fourNonzero : (2 : K) * 2 ≠ 0 :=
        Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
      apply displacementNonNull
      exact TernaryForm.cancel_scalar_of_nonzero_mul_zero
        fourNonzero fourTimesZero
    · exact ⟨sum, sumNonNull, sumDisplacementZero⟩
  · exact ⟨vector, vectorNull, displacementNonNull⟩

/-- Every nonidentity displayed ternary rotation has a constructively selected non-null seed with non-null displacement.
Six fixed coordinate tests detect the displacement quadratic form. If all six vanished, polarization would make its
image totally null; orthogonality would then make \(R-I\) form-skew and square-zero, which the explicit
three-dimensional skew calculation rules out. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitness [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (rotation : form.SpecialOrthogonal)
    (rotationNonidentity :
      rotation ≠ SpecialOrthogonal.identity form)
    (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullDisplacementWitness form rotation := by
  let basisT : Coordinates3.Vector K := ⟨1, 0, 0⟩
  let basisR : Coordinates3.Vector K := ⟨0, 1, 0⟩
  let basisS : Coordinates3.Vector K := ⟨0, 0, 1⟩
  let sumTR := Purelib.LinearAlgebra.Coordinates3.Vector.add basisT basisR
  let sumTS := Purelib.LinearAlgebra.Coordinates3.Vector.add basisT basisS
  let sumRS := Purelib.LinearAlgebra.Coordinates3.Vector.add basisR basisS
  let displacedT := (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
    basisT
  let displacedR := (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
    basisR
  let displacedS := (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
    basisS
  by_cases displacedTZero : form.quadrance displacedT = 0
  · by_cases displacedRZero : form.quadrance displacedR = 0
    · by_cases displacedSZero : form.quadrance displacedS = 0
      · by_cases sumTRZero :
          form.quadrance ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
            sumTR) = 0
        · by_cases sumTSZero :
            form.quadrance ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
              rotation) sumTS) = 0
          · by_cases sumRSZero :
              form.quadrance ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                rotation) sumRS) = 0
            · have pairingTR :
                  form.bilinear displacedT displacedR = 0 := by
                apply TernaryForm.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add displacedT displacedR
                rw [displacedTZero, displacedRZero] at addition
                have displacementSum :=
                  (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_add rotation) basisT
                    basisR
                change (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                  sumTR =
                  Purelib.LinearAlgebra.Coordinates3.Vector.add displacedT displacedR at displacementSum
                calc
                  2 * form.bilinear displacedT displacedR =
                      0 + 2 * form.bilinear displacedT displacedR + 0 := by
                    ring1
                  _ = form.quadrance
                      (Purelib.LinearAlgebra.Coordinates3.Vector.add displacedT displacedR) := addition.symm
                  _ = form.quadrance
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        sumTR) := by
                    rw [displacementSum]
                  _ = 0 := sumTRZero
              have pairingTS :
                  form.bilinear displacedT displacedS = 0 := by
                apply TernaryForm.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add displacedT displacedS
                rw [displacedTZero, displacedSZero] at addition
                have displacementSum :=
                  (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_add rotation) basisT
                    basisS
                change (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                  sumTS =
                  Purelib.LinearAlgebra.Coordinates3.Vector.add displacedT displacedS at displacementSum
                calc
                  2 * form.bilinear displacedT displacedS =
                      0 + 2 * form.bilinear displacedT displacedS + 0 := by
                    ring1
                  _ = form.quadrance
                      (Purelib.LinearAlgebra.Coordinates3.Vector.add displacedT displacedS) := addition.symm
                  _ = form.quadrance
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        sumTS) := by
                    rw [displacementSum]
                  _ = 0 := sumTSZero
              have pairingRS :
                  form.bilinear displacedR displacedS = 0 := by
                apply TernaryForm.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add displacedR displacedS
                rw [displacedRZero, displacedSZero] at addition
                have displacementSum :=
                  (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_add rotation) basisR
                    basisS
                change (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                  sumRS =
                  Purelib.LinearAlgebra.Coordinates3.Vector.add displacedR displacedS at displacementSum
                calc
                  2 * form.bilinear displacedR displacedS =
                      0 + 2 * form.bilinear displacedR displacedS + 0 := by
                    ring1
                  _ = form.quadrance
                      (Purelib.LinearAlgebra.Coordinates3.Vector.add displacedR displacedS) := addition.symm
                  _ = form.quadrance
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        sumRS) := by
                    rw [displacementSum]
                  _ = 0 := sumRSZero
              have pairingRT :
                  form.bilinear displacedR displacedT = 0 := by
                rw [form.bilinear_comm]
                exact pairingTR
              have pairingST :
                  form.bilinear displacedS displacedT = 0 := by
                rw [form.bilinear_comm]
                exact pairingTS
              have pairingSR :
                  form.bilinear displacedS displacedR = 0 := by
                rw [form.bilinear_comm]
                exact pairingRS
              have pairingTT :
                  form.bilinear displacedT displacedT = 0 :=
                displacedTZero
              have pairingRR :
                  form.bilinear displacedR displacedR = 0 :=
                displacedRZero
              have pairingSS :
                  form.bilinear displacedS displacedS = 0 :=
                displacedSZero
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingTT
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingRR
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K)) = 0
                at pairingSS
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingTR
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K)) = 0
                at pairingTS
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K)) = 0
                at pairingRS
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingRT
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨1, 0,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingST
              change form.bilinear
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 0,
                  1⟩ : Coordinates3.Vector K))
                ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation) (⟨0, 1,
                  0⟩ : Coordinates3.Vector K)) = 0
                at pairingSR
              have imagePairZero : ∀ left right : Coordinates3.Vector K,
                  form.bilinear ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                    rotation) left)
                    ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                      right) = 0 := by
                intro left right
                rw [(Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_coordinateExpansion
                  rotation) left,
                  (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement_coordinateExpansion
                    rotation) right]
                simp only [form.bilinear_add_left,
                  form.bilinear_add_right, form.bilinear_scale_left,
                  form.bilinear_scale_right]
                rw [pairingTT, pairingRR, pairingSS,
                  pairingTR, pairingTS, pairingRS, pairingRT, pairingST,
                  pairingSR]
                ring1
              have reconstruct (vector : Coordinates3.Vector K) :
                  (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) vector =
                    Purelib.LinearAlgebra.Coordinates3.Vector.add
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                      vector) vector := by
                ext <;> unfold Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                  Purelib.LinearAlgebra.Coordinates3.Vector.add
                  Coordinates3.Vector.sub <;> ring1
              have skew : ∀ left right : Coordinates3.Vector K,
                  form.bilinear ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                    rotation) left) right =
                    -form.bilinear left
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        right) := by
                intro left right
                have preserved := (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.bilinear_act
                    rotation.toIsometry) left right
                rw [reconstruct left, reconstruct right,
                  form.bilinear_add_left, form.bilinear_add_right,
                  form.bilinear_add_right, imagePairZero] at preserved
                have crossSumZero :
                    form.bilinear ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                      rotation) left) right +
                        form.bilinear left
                          ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                            rotation) right) = 0 := by
                  calc
                    form.bilinear ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                      rotation) left) right +
                        form.bilinear left
                          ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                            rotation) right) =
                      (form.bilinear
                            ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                              rotation) left)
                            ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                              rotation) right) +
                          form.bilinear
                            ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                              rotation) left) right +
                          (form.bilinear left
                              ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                                rotation) right) +
                            form.bilinear left right)) -
                        form.bilinear left right := by
                          rw [imagePairZero]
                          ring1
                    _ = 0 := by
                      rw [imagePairZero]
                      rw [preserved]
                      ring1
                calc
                  form.bilinear ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                    rotation) left) right =
                      -form.bilinear left
                          ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                            rotation) right) +
                        (form.bilinear
                            ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                              rotation) left) right +
                          form.bilinear left
                            ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                              rotation) right)) := by
                      ring1
                  _ = -form.bilinear left
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        right) := by
                    rw [crossSumZero, add_zero]
              let displacementMatrix :=
                (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacementMatrix rotation)
              have displacementSquareZero :
                  Matrix3.mul displacementMatrix displacementMatrix =
                    Purelib.LinearAlgebra.Coordinates3.Matrix3.zero := by
                apply Matrix3.eq_of_rowMul_eq
                intro vector
                have twiceZero :
                    (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                          vector) = Purelib.LinearAlgebra.Coordinates3.Vector.zero := by
                  apply form.eq_of_bilinear_eq
                  intro test
                  rw [form.bilinear_zero_left]
                  calc
                    form.bilinear
                        ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                          ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                            rotation) vector)) test =
                      -form.bilinear
                        ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                          vector)
                        ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                          test) :=
                      skew ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement
                        rotation) vector) test
                    _ = 0 := by rw [imagePairZero]; ring1
                calc
                  Purelib.LinearAlgebra.Coordinates3.Matrix3.rowMul vector
                      (Matrix3.mul displacementMatrix
                        displacementMatrix) =
                    Purelib.LinearAlgebra.Coordinates3.Matrix3.rowMul
                      (Purelib.LinearAlgebra.Coordinates3.Matrix3.rowMul vector displacementMatrix)
                      displacementMatrix :=
                    (Matrix3.rowMul_mul vector displacementMatrix
                      displacementMatrix).symm
                  _ = (Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                      ((Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.displacement rotation)
                        vector) := by
                    unfold displacementMatrix
                    rw [(Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.rowMul_displacementMatrix
                      rotation),
                      (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.rowMul_displacementMatrix
                        rotation)]
                  _ = Purelib.LinearAlgebra.Coordinates3.Vector.zero := twiceZero
                  _ = Purelib.LinearAlgebra.Coordinates3.Matrix3.rowMul vector
                    Purelib.LinearAlgebra.Coordinates3.Matrix3.zero := by
                    ext <;> unfold Purelib.LinearAlgebra.Coordinates3.Vector.zero
                      Purelib.LinearAlgebra.Coordinates3.Matrix3.rowMul Purelib.LinearAlgebra.Coordinates3.Matrix3.zero
                      <;>
                      ring1
              have displacementAntisymmetric :
                  Matrix3.IsAntisymmetric
                    (Matrix3.mul displacementMatrix form.matrix) := by
                apply form.mul_form_isAntisymmetric_of_bilinear_skew
                intro left right
                unfold displacementMatrix
                rw [(Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.rowMul_displacementMatrix rotation),
                  (Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.rowMul_displacementMatrix rotation)]
                exact skew left right
              have displacementMatrixZero :
                  displacementMatrix = Purelib.LinearAlgebra.Coordinates3.Matrix3.zero :=
                form.matrix_eq_zero_of_mul_form_antisymmetric_of_square_eq_zero
                  displacementMatrix twoNonzero displacementAntisymmetric
                  displacementSquareZero
              have matrixDifferenceZero :
                  Matrix3.sub rotation.matrix Matrix3.identity =
                    Purelib.LinearAlgebra.Coordinates3.Matrix3.zero := by
                exact displacementMatrixZero
              have rotationMatrixIdentity :
                  rotation.matrix = Matrix3.identity :=
                Matrix3.eq_of_sub_eq_zero matrixDifferenceZero
              have rotationIdentity :
                  rotation = SpecialOrthogonal.identity form := by
                apply SpecialOrthogonal.eq_of_matrix_eq
                exact rotationMatrixIdentity
              exact (rotationNonidentity rotationIdentity).elim
            · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation sumRS
                sumRSZero twoNonzero
          · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation sumTS
              sumTSZero twoNonzero
        · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation sumTR
            sumTRZero twoNonzero
      · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation basisS
          displacedSZero twoNonzero
    · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation basisR
        displacedRZero twoNonzero
  · exact Algebra.Quadratic.Ternary.Basic.TernaryForm.nonNullDisplacementWitnessOf form rotation basisT
      displacedTZero twoNonzero

set_option genInjectivity false in
/-- A retained reflection normal classifying an isometry that fixes a displayed non-null vector.

The normal remains perpendicular to the original fixed vector; its non-null certificate and matrix equality identify the
supplied isometry with reflection in that normal. -/
structure Algebra.Quadratic.Ternary.Basic.TernaryForm.FixedVectorReflectionClassification (form :
  Ternary.Basic.TernaryForm K)
    (isometry : form.Isometry) (fixedVector : Coordinates3.Vector K) where
  /-- The retained reflection normal. -/ mirror : Coordinates3.Vector K
  /-- The reflection normal has nonzero form quadrance. -/ mirrorNonNull : form.quadrance mirror ≠ 0
  /-- The retained normal is perpendicular to the originally fixed vector. -/ mirrorPerpendicular : form.Perpendicular
    mirror fixedVector
  /-- The supplied isometry matrix equals reflection in the retained normal. -/ matrix_eq : isometry.matrix =
    form.reflection mirror mirrorNonNull

constructive_injectivity Algebra.Quadratic.Ternary.Basic.TernaryForm.FixedVectorReflectionClassification

/-- Constructively classify a determinant-minus-one isometry fixing a non-null vector. Select a non-null perpendicular
test vector. If its displacement is non-null, that displacement is the mirror; if its quadrance vanishes,
orthogonal-frame reconstruction forces the displacement itself to vanish, and the relative cross supplies the mirror. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.classifyFixedVectorReflection [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (isometry : form.Isometry)
    (fixedVector : Coordinates3.Vector K)
    (fixedVectorNonNull : form.quadrance fixedVector ≠ 0)
    (fixed : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) fixedVector = fixedVector)
    (determinantMinusOne :
      Matrix3.determinant isometry.matrix = -1)
    (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.FixedVectorReflectionClassification form isometry fixedVector := by
  let selected :=
    form.perpendicularNonNullVectorWitness fixedVector
      fixedVectorNonNull twoNonzero
  let test := selected.value
  let difference :=
    Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test
  have testNonNull : form.quadrance test ≠ 0 := selected.nonNull
  have testPerpendicularFixed :
      form.Perpendicular test fixedVector := selected.perpendicular
  have fixedPerpendicularTest :
      form.Perpendicular fixedVector test :=
    (form.perpendicular_comm fixedVector test).2 testPerpendicularFixed
  have actedTestPerpendicularFixed :
      form.Perpendicular ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) fixedVector := by
    unfold Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.Perpendicular
    calc
      form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) fixedVector =
          form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test)
            ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) fixedVector) := by
        rw [fixed]
      _ = form.bilinear test fixedVector :=
        (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.bilinear_act isometry) test fixedVector
      _ = 0 := testPerpendicularFixed
  have differencePerpendicularFixed :
      form.Perpendicular difference fixedVector := by
    change
      form.bilinear
        ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test)
        fixedVector = 0 at actedTestPerpendicularFixed
    change form.bilinear test fixedVector = 0 at testPerpendicularFixed
    change form.bilinear difference fixedVector = 0
    unfold difference
    rw [form.bilinear_sub_left, actedTestPerpendicularFixed,
      testPerpendicularFixed]
    ring1
  have fixedPerpendicularDifference :
      form.Perpendicular fixedVector difference :=
    (form.perpendicular_comm fixedVector difference).2
      differencePerpendicularFixed
  by_cases differenceNull : form.quadrance difference = 0
  · have subtraction := form.quadrance_sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test)
      test
    change form.quadrance difference = _ at subtraction
    rw [differenceNull, (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.quadrance_act isometry)] at subtraction
    have twicePairing :
        2 * form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test =
          2 * form.quadrance test := by
      calc
        2 * form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test =
            2 * form.quadrance test -
              (form.quadrance test -
                2 * form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test +
                form.quadrance test) := by
          ring1
        _ = 2 * form.quadrance test := by
          rw [← subtraction]
          ring1
    have pairing :
        form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test =
          form.quadrance test :=
      TernaryForm.scalar_eq_of_nonzero_mul_eq_mul_direct twoNonzero twicePairing
    have differencePerpendicularTest :
        form.Perpendicular difference test := by
      unfold Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.Perpendicular difference
      rw [form.bilinear_sub_left]
      change form.bilinear ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test -
        form.quadrance test = 0
      rw [pairing]
      ring1
    let third := form.cross fixedVector test
    have thirdNonNull : form.quadrance third ≠ 0 :=
      form.cross_nonNull_of_perpendicular fixedVector test
        fixedVectorNonNull testNonNull fixedPerpendicularTest
    have fixedPerpendicularThird :
        form.Perpendicular fixedVector third := by
      apply (form.perpendicular_comm fixedVector third).2
      exact form.cross_perpendicular_left fixedVector test
    have testPerpendicularThird :
        form.Perpendicular test third := by
      apply (form.perpendicular_comm test third).2
      exact form.cross_perpendicular_right fixedVector test
    let coefficient :=
      form.bilinear difference third / form.quadrance third
    have differenceScale :
        difference = Purelib.LinearAlgebra.Coordinates3.Vector.scale coefficient third := by
      have reconstruction := form.orthogonalFrame_reconstruct
        fixedVector test third fixedVectorNonNull testNonNull thirdNonNull
        fixedPerpendicularTest fixedPerpendicularThird
        testPerpendicularThird difference
      have differenceFixedZero :
          form.bilinear difference fixedVector = 0 :=
        differencePerpendicularFixed
      have differenceTestZero :
          form.bilinear difference test = 0 :=
        differencePerpendicularTest
      calc
        difference =
            Purelib.LinearAlgebra.Coordinates3.Vector.add
              (Purelib.LinearAlgebra.Coordinates3.Vector.add
                (Purelib.LinearAlgebra.Coordinates3.Vector.scale
                  (form.bilinear difference fixedVector /
                    form.quadrance fixedVector) fixedVector)
                (Purelib.LinearAlgebra.Coordinates3.Vector.scale
                  (form.bilinear difference test /
                    form.quadrance test) test))
              (Purelib.LinearAlgebra.Coordinates3.Vector.scale
                (form.bilinear difference third /
                  form.quadrance third) third) :=
          reconstruction.symm
        _ = Purelib.LinearAlgebra.Coordinates3.Vector.scale coefficient third := by
          rw [differenceFixedZero, differenceTestZero,
            Algebra.Field.ExplicitField.zero_div, Algebra.Field.ExplicitField.zero_div]
          ext <;> unfold coefficient Purelib.LinearAlgebra.Coordinates3.Vector.add
            Purelib.LinearAlgebra.Coordinates3.Vector.scale <;> ring1
    have coefficientSquareTimesZero :
        coefficient ^ 2 * form.quadrance third = 0 := by
      calc
        coefficient ^ 2 * form.quadrance third =
            form.quadrance (Purelib.LinearAlgebra.Coordinates3.Vector.scale coefficient third) :=
          (form.quadrance_scale coefficient third).symm
        _ = form.quadrance difference := by rw [differenceScale]
        _ = 0 := differenceNull
    have coefficientSquareZero : coefficient * coefficient = 0 := by
      apply TernaryForm.cancel_scalar_of_nonzero_mul_zero thirdNonNull
      calc
        form.quadrance third * (coefficient * coefficient) =
            coefficient ^ 2 * form.quadrance third := by
          ring1
        _ = 0 := coefficientSquareTimesZero
    have coefficientZero : coefficient = 0 := by
      by_cases zero : coefficient = 0
      · exact zero
      · have productNonzero :=
          Algebra.Field.ExplicitField.mul_ne_zero zero zero
        exact (productNonzero coefficientSquareZero).elim
    have differenceIsZero : difference = Coordinates3.Vector.zero := by
      rw [differenceScale, coefficientZero, Coordinates3.Vector.zero_scale]
    have testFixed : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test = test := by
      calc
        (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test =
            Coordinates3.Vector.add difference test := by
          ext <;> unfold difference Purelib.LinearAlgebra.Coordinates3.Vector.add
            Purelib.LinearAlgebra.Coordinates3.Vector.sub <;> ring1
        _ = Purelib.LinearAlgebra.Coordinates3.Vector.add Coordinates3.Vector.zero test := by rw [differenceIsZero]
        _ = test := Coordinates3.Vector.zero_add test
    let reflection := form.reflectionIsometry third thirdNonNull
    let product := Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.mul isometry reflection
    have productDeterminantOne :
        Matrix3.determinant product.matrix = 1 := by
      change Matrix3.determinant
        (Matrix3.mul isometry.matrix
          (form.reflection third thirdNonNull)) = 1
      rw [Matrix3.determinant_mul, determinantMinusOne,
        form.determinant_reflection]
      ring1
    have productFixesFixed : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act product) fixedVector =
        fixedVector := by
      rw [Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act_mul, fixed]
      change Matrix3.rowMul fixedVector
        (form.reflection third thirdNonNull) = fixedVector
      apply form.rowMul_reflection_of_perpendicular
      exact fixedPerpendicularThird
    have productFixesTest : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act product) test = test := by
      rw [Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act_mul, testFixed]
      change Matrix3.rowMul test
        (form.reflection third thirdNonNull) = test
      apply form.rowMul_reflection_of_perpendicular
      exact testPerpendicularThird
    have productIdentity :
        product.matrix = Matrix3.identity :=
      Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.matrix_eq_identity_of_fixed_orthogonal_pair
        form product fixedVector test fixedVectorNonNull testNonNull
        fixedPerpendicularTest productFixesFixed productFixesTest
        productDeterminantOne
    have matrixEq :
        isometry.matrix = form.reflection third thirdNonNull := by
      calc
        isometry.matrix =
            Matrix3.mul isometry.matrix Matrix3.identity := by
          rw [Matrix3.mul_identity]
        _ = Matrix3.mul isometry.matrix
            (Matrix3.mul
              (form.reflection third thirdNonNull)
              (form.reflection third thirdNonNull)) := by
          rw [form.reflection_square]
        _ = Matrix3.mul
            (Matrix3.mul isometry.matrix
              (form.reflection third thirdNonNull))
            (form.reflection third thirdNonNull) := by
          rw [Matrix3.mul_assoc]
        _ = Matrix3.mul Matrix3.identity
            (form.reflection third thirdNonNull) := by
          exact congrArg
            (fun matrix => Matrix3.mul matrix
              (form.reflection third thirdNonNull))
            productIdentity
        _ = form.reflection third thirdNonNull :=
          Matrix3.identity_mul _
    exact
      { mirror := third
        mirrorNonNull := thirdNonNull
        mirrorPerpendicular :=
          form.cross_perpendicular_left fixedVector test
        matrix_eq := matrixEq }
  · let reflection := form.reflectionIsometry difference differenceNull
    let product := Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.mul isometry reflection
    have productDeterminantOne :
        Matrix3.determinant product.matrix = 1 := by
      change Matrix3.determinant
        (Matrix3.mul isometry.matrix
          (form.reflection difference differenceNull)) = 1
      rw [Matrix3.determinant_mul, determinantMinusOne,
        form.determinant_reflection]
      ring1
    have productFixesFixed : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act product) fixedVector =
        fixedVector := by
      rw [Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act_mul, fixed]
      change Matrix3.rowMul fixedVector
        (form.reflection difference differenceNull) = fixedVector
      apply form.rowMul_reflection_of_perpendicular
      exact fixedPerpendicularDifference
    have productFixesTest : (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act product) test = test := by
      rw [Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act_mul]
      change Matrix3.rowMul ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test)
        (form.reflection
          (Coordinates3.Vector.sub
            ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act isometry) test) test) differenceNull) =
              test
      apply form.rowMul_reflection_difference
      exact (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.quadrance_act isometry) test
    have productIdentity :
        product.matrix = Matrix3.identity :=
      Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.matrix_eq_identity_of_fixed_orthogonal_pair
        form product fixedVector test fixedVectorNonNull testNonNull
        fixedPerpendicularTest productFixesFixed productFixesTest
        productDeterminantOne
    have matrixEq :
        isometry.matrix = form.reflection difference differenceNull := by
      calc
        isometry.matrix =
            Matrix3.mul isometry.matrix Matrix3.identity := by
          rw [Matrix3.mul_identity]
        _ = Matrix3.mul isometry.matrix
            (Matrix3.mul
              (form.reflection difference differenceNull)
              (form.reflection difference differenceNull)) := by
          rw [form.reflection_square]
        _ = Matrix3.mul
            (Matrix3.mul isometry.matrix
              (form.reflection difference differenceNull))
            (form.reflection difference differenceNull) := by
          rw [Matrix3.mul_assoc]
        _ = Matrix3.mul Matrix3.identity
            (form.reflection difference differenceNull) := by
          exact congrArg
            (fun matrix => Matrix3.mul matrix
              (form.reflection difference differenceNull))
            productIdentity
        _ = form.reflection difference differenceNull :=
          Matrix3.identity_mul _
    exact
      { mirror := difference
        mirrorNonNull := differenceNull
        mirrorPerpendicular := differencePerpendicularFixed
        matrix_eq := matrixEq }

set_option genInjectivity false in
/-- A displayed rotation factored into two half turns about retained non-null axes.

The original ordered axes and their quadrance certificates are cached together with equality of their row-order product
to the supplied rotation. -/
structure Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization (form :
  Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  /-- The first retained half-turn axis. -/ firstAxis : Coordinates3.Vector K
  /-- The first retained axis has nonzero form quadrance. -/ firstNonNull : form.quadrance firstAxis ≠ 0
  /-- The second retained half-turn axis. -/ secondAxis : Coordinates3.Vector K
  /-- The second retained axis has nonzero form quadrance. -/ secondNonNull : form.quadrance secondAxis ≠ 0
  /-- The row-order product of the two retained half turns is the original rotation. -/ rotation_eq :
    SpecialOrthogonal.mul
        (form.halfTurnRotation firstAxis firstNonNull)
        (form.halfTurnRotation secondAxis secondNonNull) = rotation

constructive_injectivity Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization

/-- The identity has a canonical executable two-half-turn factorization: select one of the six certified non-null
coordinate candidates and use its involutive half turn twice. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization form (SpecialOrthogonal.identity form) := by
  let selected := form.nonNullVectorWitness twoNonzero
  exact
    { firstAxis := selected.value
      firstNonNull := selected.nonNull
      secondAxis := selected.value
      secondNonNull := selected.nonNull
      rotation_eq := by
        apply SpecialOrthogonal.eq_of_matrix_eq
        exact form.halfTurn_square selected.value selected.nonNull }

/-- Every displayed ternary rotation in characteristic different from two has an executable factorization into two half
turns about non-null axes. For a nonidentity rotation, the first reflection reduction fixes a selected non-null seed;
the fixed-vector classifier supplies the second reflection, and the two minus signs converting reflections to half turns
cancel. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.twoHalfTurnFactorization [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization form rotation := by
  by_cases rotationMatrixIdentity :
      rotation.matrix = Matrix3.identity
  · have rotationIdentity :
        rotation = SpecialOrthogonal.identity form := by
      apply SpecialOrthogonal.eq_of_matrix_eq
      exact rotationMatrixIdentity
    subst rotation
    exact Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization form twoNonzero
  · let displaced :=
      form.nonNullDisplacementWitness rotation (by
        intro rotationIdentity
        apply rotationMatrixIdentity
        exact congrArg (fun value : form.SpecialOrthogonal => value.matrix)
          rotationIdentity) twoNonzero
    let reduction :=
      form.displacementReflectionReduction rotation displaced.seed
        displaced.seedNonNull displaced.displacementNonNull
    let classification :=
      Algebra.Quadratic.Ternary.Basic.TernaryForm.classifyFixedVectorReflection form reduction.reduced reduction.seed
        reduction.seedNonNull reduction.seedFixed
        reduction.determinantMinusOne twoNonzero
    have reducedMatrix :
        reduction.reduced.matrix =
          Matrix3.mul rotation.matrix
            (form.reflection reduction.mirror reduction.mirrorNonNull) := by
      exact congrArg (fun isometry : form.Isometry => isometry.matrix)
        reduction.reduced_eq
    exact
      { firstAxis := classification.mirror
        firstNonNull := classification.mirrorNonNull
        secondAxis := reduction.mirror
        secondNonNull := reduction.mirrorNonNull
        rotation_eq := by
          apply SpecialOrthogonal.eq_of_matrix_eq
          change Matrix3.mul
              (form.halfTurn classification.mirror
                classification.mirrorNonNull)
              (form.halfTurn reduction.mirror reduction.mirrorNonNull) =
            rotation.matrix
          unfold Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.halfTurn
          rw [Matrix3.mul_neg_neg]
          calc
            Matrix3.mul
                (form.reflection classification.mirror
                  classification.mirrorNonNull)
                (form.reflection reduction.mirror reduction.mirrorNonNull) =
              Matrix3.mul reduction.reduced.matrix
                (form.reflection reduction.mirror reduction.mirrorNonNull) := by
                rw [classification.matrix_eq]
            _ = Matrix3.mul
                (Matrix3.mul rotation.matrix
                  (form.reflection reduction.mirror reduction.mirrorNonNull))
                (form.reflection reduction.mirror reduction.mirrorNonNull) := by
              rw [reducedMatrix]
            _ = Matrix3.mul rotation.matrix
                (Matrix3.mul
                  (form.reflection reduction.mirror reduction.mirrorNonNull)
                  (form.reflection reduction.mirror reduction.mirrorNonNull)) := by
              rw [Matrix3.mul_assoc]
            _ = Matrix3.mul rotation.matrix Matrix3.identity := by
              rw [form.reflection_square]
            _ = rotation.matrix := Matrix3.mul_identity rotation.matrix }

section TwoHalfTurnFactorization

/-- The product of the two cached pure-vector Clifford representatives. -/
def Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage {form :
  Ternary.Basic.TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (factorization : Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization form rotation) :
    form.NonNullEvenClifford :=
  NonNullEvenClifford.mul
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form factorization.firstAxis
      factorization.firstNonNull)
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnValue form factorization.secondAxis
      factorization.secondNonNull)

/-- A cached two-half-turn factorization computes an explicit Clifford preimage of its rotation. -/
theorem
  Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage_actionRotation
  {form : Ternary.Basic.TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (factorization : Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization form rotation) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage factorization)) =
      rotation := by
  calc
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage factorization)) =
        SpecialOrthogonal.mul
          (form.halfTurnRotation factorization.firstAxis
            factorization.firstNonNull)
          (form.halfTurnRotation factorization.secondAxis
            factorization.secondNonNull) :=
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.halfTurnRotation_mul form
        factorization.firstAxis factorization.secondAxis
        factorization.firstNonNull factorization.secondNonNull).symm
    _ = rotation := factorization.rotation_eq

/-- The Clifford preimage constructed for the identity rotation is projectively equivalent to the identity. -/
theorem
  Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.identity_cliffordPreimage_equivalent_identity
  [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    (NonNullEvenClifford.Equivalent
      (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage
      (Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization form twoNonzero)))
      (NonNullEvenClifford.identity form) := by
  apply (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_eq_iff_equivalent
    (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage
      (Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization form twoNonzero))
    (NonNullEvenClifford.identity form) twoNonzero).1
  calc
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage
      (Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization form twoNonzero))) =
        SpecialOrthogonal.identity form :=
      (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage_actionRotation
        (Algebra.Quadratic.Ternary.Basic.TernaryForm.identityTwoHalfTurnFactorization form twoNonzero))
    _ = (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (NonNullEvenClifford.identity
      form)) :=
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_identity form).symm

end TwoHalfTurnFactorization

set_option genInjectivity false in
/-- An executable two-half-turn factorization for every displayed rotation of a ternary form.

The factor function returns both original axes, their denominator certificates and the product equality for the actual
supplied rotation. -/
structure Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration (form :
  Ternary.Basic.TernaryForm K) where
  /-- Compute two non-null axes and the factorization certificate for each rotation. -/ factor : (rotation :
    form.SpecialOrthogonal) →
    Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnFactorization form rotation

constructive_injectivity Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration

/-- The unconditional finite two-half-turn generation algorithm obtained by running the constructive factorization above
on every displayed rotation. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.twoHalfTurnGeneration [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration form where
  factor := fun rotation =>
    Algebra.Quadratic.Ternary.Basic.TernaryForm.twoHalfTurnFactorization form rotation twoNonzero

section TwoHalfTurnGeneration

/-- Explicit Clifford representative computed by the cached factorization algorithm. -/
def Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.cliffordPreimage {form :
  Ternary.Basic.TernaryForm K}
    (generation : Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration form)
    (rotation : form.SpecialOrthogonal) : form.NonNullEvenClifford :=
  (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage (generation.factor
    rotation))

/-- The Clifford preimage computed from the retained factorization acts as the requested rotation. -/
theorem
  Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.cliffordPreimage_actionRotation
  {form : Ternary.Basic.TernaryForm K}
    (generation : Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration form)
    (rotation : form.SpecialOrthogonal) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      ((Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.cliffordPreimage generation) rotation)) =
      rotation :=
  (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage_actionRotation
    (generation.factor rotation))

end TwoHalfTurnGeneration

set_option genInjectivity false in
/-- A projective Clifford correspondence with executable rotation preimages and characterized fibers.

The preimage retains the original non-null Clifford representative and its action equation. Equality of two actions is
equivalent to a displayed nonzero homogeneous scaling of their original representatives. -/
structure Algebra.Quadratic.Ternary.Basic.TernaryForm.ProjectiveCliffordCorrespondence (form :
  Ternary.Basic.TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  /-- The executable Clifford representative assigned to each displayed rotation. -/ preimage : form.SpecialOrthogonal →
    form.NonNullEvenClifford
  /-- The retained Clifford preimage acts as the original rotation. -/ action_preimage : ∀ rotation :
    form.SpecialOrthogonal,
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation (preimage rotation)) = rotation
  /-- Two Clifford representatives have the same action exactly when related by nonzero homogeneous scaling. -/
    action_eq_iff_equivalent :
    ∀ left right : form.NonNullEvenClifford,
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation left) =
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation right) ↔
        (NonNullEvenClifford.Equivalent left) right

constructive_injectivity Algebra.Quadratic.Ternary.Basic.TernaryForm.ProjectiveCliffordCorrespondence

/-- Once the finite two-half-turn algorithm is supplied, the Clifford action is constructively surjective and
projectively faithful. This isolates the remaining general-form work in one explicit factorization interface. -/
def
  Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.projectiveCliffordCorrespondence
    {form : Ternary.Basic.TernaryForm K} (generation : Algebra.Quadratic.Ternary.Basic.TernaryForm.TwoHalfTurnGeneration
      form)
    (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.ProjectiveCliffordCorrespondence form twoNonzero where
  preimage := (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.cliffordPreimage generation)
  action_preimage :=
    (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.cliffordPreimage_actionRotation generation)
  action_eq_iff_equivalent := fun left right =>
    Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation_eq_iff_equivalent
      left right twoNonzero

/-- The unconditional generalized projective rotation theorem for every displayed nondegenerate ternary form in
characteristic different from two. It contains an executable Clifford preimage for every special-orthogonal matrix and
the exact nonzero-scale description of every fiber. -/
def Algebra.Quadratic.Ternary.Basic.TernaryForm.projectiveCliffordCorrespondence [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    Algebra.Quadratic.Ternary.Basic.TernaryForm.ProjectiveCliffordCorrespondence form twoNonzero :=
  (Geometry.Rotations.Ternary.Clifford.TernaryForm.TwoHalfTurnGeneration.projectiveCliffordCorrespondence
    (Algebra.Quadratic.Ternary.Basic.TernaryForm.twoHalfTurnGeneration form twoNonzero))
    twoNonzero

/-- Pointwise surjectivity extracted from the constructive projective Clifford correspondence. -/
theorem Algebra.Quadratic.Ternary.Basic.TernaryForm.cliffordAction_surjective [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0)
    (rotation : form.SpecialOrthogonal) :
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.actionRotation
      ((Algebra.Quadratic.Ternary.Basic.TernaryForm.projectiveCliffordCorrespondence form twoNonzero).preimage
        rotation)) = rotation :=
  (Algebra.Quadratic.Ternary.Basic.TernaryForm.projectiveCliffordCorrespondence form twoNonzero).action_preimage
    rotation

end TernaryForm

end Purelib

end

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

namespace TwoHalfTurnFactorization

/-- Recover a nonzero fixed direction from the retained two-half-turn factorization.

The cached Clifford preimage supplies its vector part unless it is scalar.
In the scalar case, the original first axis is retained as the nonzero fixed
vector. The certificate refers to the original rotation matrix.
-/
@[expose] def fixedDirection [DecidableEq K] {form : TernaryForm K}
    {rotation : form.SpecialOrthogonal} (factorization : form.TwoHalfTurnFactorization rotation) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector rotation.matrix = vector := by
  let value := Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage factorization
  have fallbackNonzero : factorization.firstAxis ≠ Vector3.zero := by
    intro axisZero
    apply factorization.firstNonNull
    rw [axisZero, form.quadrance_zero]
  let fixed := NonNullEvenClifford.fixedVector value factorization.firstAxis fallbackNonzero
  refine ⟨fixed.1, fixed.2.1, ?_⟩
  have represented := Clifford.TernaryForm.TwoHalfTurnFactorization.cliffordPreimage_actionRotation factorization
  have matrixEqual := congrArg (fun result : form.SpecialOrthogonal => result.matrix) represented
  change NonNullEvenClifford.actionMatrix value = rotation.matrix at matrixEqual
  rw [← matrixEqual]
  exact fixed.2.2

end TwoHalfTurnFactorization

/-- Construct a nonzero fixed direction for every displayed ternary rotation.

Nonzero two and executable scalar equality supply the constructive
factorization. Its retained axes and Clifford preimage determine the direction
without selecting an eigenvector through a choice principle.
-/
@[expose] def fixedDirection [DecidableEq K] (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector rotation.matrix = vector :=
  (form.twoHalfTurnFactorization rotation twoNonzero).fixedDirection

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
