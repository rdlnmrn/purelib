module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Explicit even Clifford algebra of a ternary form

The four coordinates are stored as one scalar and one displayed vector.  The
product uses the cached adjugate of the form matrix, so it is polynomial in
the supplied finite data and performs no fresh matrix inversion.
-/

section

variable {K : Type*} [ExplicitField K]

section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

/-- A zero product with a supplied nonzero left factor forces its right factor to be zero. -/
private theorem scalar_eq_zero_of_nonzero_mul_eq_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- Cancel a supplied nonzero left factor from equal scalar products. -/
private theorem scalar_eq_of_nonzero_mul_eq_mul {factor left
  right : K}
    (factorNonzero : factor ≠ 0)
    (equal : factor * left = factor * right) : left = right := by
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = (factor * factor⁻¹) * left := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [equal]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- Cancel a supplied nonzero left factor from equal scalar products. -/
theorem scalar_eq_of_nonzero_mul_eq_mul_direct {factor left
  right : K}
    (factorNonzero : factor ≠ 0)
    (equal : factor * left = factor * right) : left = right := by
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = (factor * factor⁻¹) * left := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [equal]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- Compute the denominator-free cross product using the retained adjugate.

The ordinary coordinate cross is multiplied by the cached adjugate, producing the determinant-scaled form-relative cross
without recomputing an inverse. -/
def cliffordCross (form : Form K) (left right : Vector3 K) :
  Vector3 K :=
  Matrix3.rowMul (Vector3.cross left right) form.adjugate

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

/-- The adjugate cross is the determinant-scaled form-relative cross. -/
theorem cliffordCross_eq_scale_cross (form : Form K)
    (left right : Vector3 K) :
    form.cliffordCross left right =
      Vector3.scale form.determinant (form.cross left right) := by
  have cancel : form.determinant * form.determinant⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel form.determinant
      form.determinantNonzero
  unfold Form.cliffordCross Form.cross
  rw [form.inverse_eq_scale_adjugate]
  rw [Matrix3.rowMul_scale]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [Vector3.scale_scale]
  have coefficient : form.determinant * (1 * form.determinant⁻¹) =
      (1 : K) := by
    calc
      form.determinant * (1 * form.determinant⁻¹) =
          form.determinant * form.determinant⁻¹ := by ring1
      _ = 1 := cancel
  rw [coefficient, Vector3.one_scale]

/-- Multiplying the denominator-free relative cross by the form matrix
recovers the ordinary cross, scaled only by the cached determinant. -/
theorem rowMul_cliffordCross_matrix (form : Form K)
    (left right : Vector3 K) :
    Matrix3.rowMul (form.cliffordCross left right) form.matrix =
      Vector3.scale form.determinant (Vector3.cross left right) := by
  unfold Form.cliffordCross
  rw [Matrix3.rowMul_mul, form.adjugate_mul_matrix,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity]

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic in
/-- A displayed vector whose Clifford cross with every test vector vanishes is zero.

The retained adjugate and nonzero determinant reduce the claim to the ordinary
coordinate cross. Two supplied coordinate vectors determine all three axis
entries, using scalar inverse cancellation without choosing a basis extension. -/
theorem eq_zero_of_cliffordCross_right_eq_zero (form : Form
  K)
    (axis : Vector3 K)
    (annihilated : ∀ vector : Vector3 K,
      form.cliffordCross vector axis = Vector3.zero) :
    axis = Vector3.zero := open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in by
  have ordinaryCrossZero : ∀ vector : Vector3 K,
      Vector3.cross vector axis = Vector3.zero := by
    intro vector
    have scaledCrossZero :
        Vector3.scale form.determinant (Vector3.cross vector axis) =
          Vector3.zero := by
      calc
        Vector3.scale form.determinant (Vector3.cross vector axis) =
            Matrix3.rowMul (form.cliffordCross vector axis) form.matrix :=
          (form.rowMul_cliffordCross_matrix vector axis).symm
        _ = Matrix3.rowMul Vector3.zero form.matrix := by
          rw [annihilated vector]
        _ = Vector3.zero := by
          ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1
    apply Vector3.ext
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector3.scale_t, Vector3.zero_t] using
        congrArg Vector3.t scaledCrossZero
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector3.scale_r, Vector3.zero_r] using
        congrArg Vector3.r scaledCrossZero
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector3.scale_s, Vector3.zero_s] using
        congrArg Vector3.s scaledCrossZero
  have first := ordinaryCrossZero (⟨1, 0, 0⟩ : Vector3 K)
  have second := ordinaryCrossZero (⟨0, 1, 0⟩ : Vector3 K)
  have axisS : axis.s = 0 := by
    have coordinate := congrArg Vector3.r first
    have negativeZero : -axis.s = 0 := by
      calc
        -axis.s = (Vector3.cross (⟨1, 0, 0⟩ : Vector3 K) axis).r := by
          unfold Vector3.cross
          ring1
        _ = 0 := coordinate
    have cancel := AddGroup.neg_add_cancel axis.s
    rewrite [negativeZero, zero_add] at cancel
    exact cancel
  have axisR : axis.r = 0 := by
    have coordinate := congrArg Vector3.s first
    calc
      axis.r = (Vector3.cross (⟨1, 0, 0⟩ : Vector3 K) axis).s := by
        unfold Vector3.cross
        ring1
      _ = 0 := coordinate
  have axisT : axis.t = 0 := by
    have coordinate := congrArg Vector3.s second
    have negativeZero : -axis.t = 0 := by
      calc
        -axis.t = (Vector3.cross (⟨0, 1, 0⟩ : Vector3 K) axis).s := by
          unfold Vector3.cross
          ring1
        _ = 0 := coordinate
    have cancel := AddGroup.neg_add_cancel axis.t
    rewrite [negativeZero, zero_add] at cancel
    exact cancel
  apply Vector3.ext
  · exact axisT
  · exact axisR
  · exact axisS

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

/-- The adjugate cross product is zero when its left argument is zero. -/
@[simp] theorem cliffordCross_zero_left (form : Form K)
    (vector : Vector3 K) :
    form.cliffordCross Vector3.zero vector = Vector3.zero := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.zero Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product is zero when its right argument is zero. -/
@[simp] theorem cliffordCross_zero_right (form : Form K)
    (vector : Vector3 K) :
    form.cliffordCross vector Vector3.zero = Vector3.zero := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.zero Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product of a vector with itself is zero. -/
@[simp] theorem cliffordCross_self (form : Form K)
    (vector : Vector3 K) :
    form.cliffordCross vector vector = Vector3.zero := by
  ext <;> unfold Form.cliffordCross Vector3.cross Matrix3.rowMul Vector3.zero <;>
    ring1

/-- Interchanging the two inputs negates the adjugate cross product. -/
theorem cliffordCross_anticomm (form : Form K)
    (left right : Vector3 K) :
    form.cliffordCross left right =
      Vector3.neg (form.cliffordCross right left) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Matrix3.rowMul Vector3.neg <;>
    ring1

/-- The adjugate cross product respects addition in its left argument. -/
theorem cliffordCross_add_left (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross (Vector3.add first second) third =
      Vector3.add (form.cliffordCross first third)
        (form.cliffordCross second third) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.add Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects addition in its right argument. -/
theorem cliffordCross_add_right (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross first (Vector3.add second third) =
      Vector3.add (form.cliffordCross first second)
        (form.cliffordCross first third) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.add Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects subtraction in its left argument. -/
theorem cliffordCross_sub_left (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross (Vector3.sub first second) third =
      Vector3.sub (form.cliffordCross first third)
        (form.cliffordCross second third) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.sub Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects subtraction in its right argument. -/
theorem cliffordCross_sub_right (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross first (Vector3.sub second third) =
      Vector3.sub (form.cliffordCross first second)
        (form.cliffordCross first third) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.sub Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects scalar multiplication in its left argument. -/
theorem cliffordCross_scale_left (form : Form K) (scalar : K)
    (left right : Vector3 K) :
    form.cliffordCross (Vector3.scale scalar left) right =
      Vector3.scale scalar (form.cliffordCross left right) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.scale Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects scalar multiplication in its right argument. -/
theorem cliffordCross_scale_right (form : Form K) (scalar :
  K)
    (left right : Vector3 K) :
    form.cliffordCross left (Vector3.scale scalar right) =
      Vector3.scale scalar (form.cliffordCross left right) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.scale Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects negation in its left argument. -/
theorem cliffordCross_neg_left (form : Form K)
    (left right : Vector3 K) :
    form.cliffordCross (Vector3.neg left) right =
      Vector3.neg (form.cliffordCross left right) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.neg Matrix3.rowMul <;>
    ring1

/-- The adjugate cross product respects negation in its right argument. -/
theorem cliffordCross_neg_right (form : Form K)
    (left right : Vector3 K) :
    form.cliffordCross left (Vector3.neg right) =
      Vector3.neg (form.cliffordCross left right) := by
  ext <;> unfold Form.cliffordCross Vector3.cross Vector3.neg Matrix3.rowMul <;>
    ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

/-- The adjugate cross has the determinant-scaled scalar triple product. -/
theorem bilinear_cliffordCross (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear (form.cliffordCross first second) third =
      form.determinant * Vector3.determinant first second third := by
  rw [form.cliffordCross_eq_scale_cross,
    form.bilinear_scale_left, form.bilinear_cross]

/-- Cyclically move the three arguments of a bilinear adjugate-cross pairing. -/
theorem bilinear_cliffordCross_cyclic (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear (form.cliffordCross first second) third =
      form.bilinear first (form.cliffordCross second third) := by
  rw [form.bilinear_cliffordCross,
    form.bilinear_comm first (form.cliffordCross second third),
    form.bilinear_cliffordCross]
  congr 1
  unfold Vector3.determinant
  ring1

/-- The adjugate cross product is perpendicular to its left input in the retained form. -/
theorem cliffordCross_perpendicular_left (form : Form K)
    (left right : Vector3 K) :
    form.Perpendicular (form.cliffordCross left right) left := by
  rw [form.cliffordCross_eq_scale_cross]
  exact form.perpendicular_scale_left form.determinant
    (form.cross left right) left (form.cross_perpendicular_left left right)

/-- The adjugate cross product is perpendicular to its right input in the retained form. -/
theorem cliffordCross_perpendicular_right (form : Form K)
    (left right : Vector3 K) :
    form.Perpendicular (form.cliffordCross left right) right := by
  rw [form.cliffordCross_eq_scale_cross]
  exact form.perpendicular_scale_left form.determinant
    (form.cross left right) right (form.cross_perpendicular_right left right)

/-- The adjugate cross has the determinant-scaled Lagrange quadrance. -/
theorem quadrance_cliffordCross (form : Form K)
    (left right : Vector3 K) :
    form.quadrance (form.cliffordCross left right) =
      form.determinant *
        (form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2) := by
  have lagrange := form.lagrange left right
  have remainder :
      form.determinant * form.quadrance (form.cross left right) =
        form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2 := by
    calc
      form.determinant * form.quadrance (form.cross left right) =
          form.bilinear left right ^ 2 +
              form.determinant * form.quadrance (form.cross left right) -
            form.bilinear left right ^ 2 := by ring1
      _ = form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2 := by rw [lagrange]
  rw [form.cliffordCross_eq_scale_cross, form.quadrance_scale]
  calc
    form.determinant ^ 2 * form.quadrance (form.cross left right) =
        form.determinant *
          (form.determinant * form.quadrance (form.cross left right)) := by
      ring1
    _ = form.determinant *
        (form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2) := by rw [remainder]

/-- Determinant-scaled Binet--Cauchy for two adjugate crosses. -/
theorem bilinear_cliffordCross_pair (form : Form K)
    (first second third fourth : Vector3 K) :
    form.bilinear (form.cliffordCross first second)
        (form.cliffordCross third fourth) =
      form.determinant *
        (form.bilinear first third * form.bilinear second fourth -
          form.bilinear first fourth * form.bilinear second third) := by
  have binet := form.binet_cauchy first second third fourth
  rw [form.cliffordCross_eq_scale_cross,
    form.cliffordCross_eq_scale_cross,
    form.bilinear_scale_left, form.bilinear_scale_right]
  calc
    form.determinant *
        (form.determinant *
          form.bilinear (form.cross first second)
            (form.cross third fourth)) =
      form.determinant *
        (form.bilinear first third * form.bilinear second fourth -
          form.bilinear first fourth * form.bilinear second third) := by
      rw [binet]

/-- The mixed adjugate-cross terms in the Clifford action cancel. -/
theorem bilinear_cliffordCross_swap (form : Form K)
    (first second axis : Vector3 K) :
    form.bilinear first (form.cliffordCross second axis) =
      -form.bilinear (form.cliffordCross first axis) second := by
  rw [form.bilinear_comm first (form.cliffordCross second axis),
    form.bilinear_cliffordCross, form.bilinear_cliffordCross]
  unfold Vector3.determinant
  ring1

/-- Right-nested adjugate cross identity. -/
theorem cliffordCross_vector_triple (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross first (form.cliffordCross second third) =
      Vector3.sub
        (Vector3.scale
          (form.determinant * form.bilinear first third) second)
        (Vector3.scale
          (form.determinant * form.bilinear first second) third) := by
  calc
    form.cliffordCross first (form.cliffordCross second third) =
      Vector3.scale form.determinant
        (form.cross first (form.cliffordCross second third)) :=
      form.cliffordCross_eq_scale_cross first
        (form.cliffordCross second third)
    _ = Vector3.scale form.determinant
        (form.cross first
          (Vector3.scale form.determinant (form.cross second third))) := by
      rw [form.cliffordCross_eq_scale_cross]
    _ = Vector3.scale form.determinant
        (Vector3.scale form.determinant
          (form.cross first (form.cross second third))) := by
      rw [form.cross_scale_right]
    _ = Vector3.scale form.determinant
        (Vector3.sub
          (Vector3.scale (form.bilinear first third) second)
          (Vector3.scale (form.bilinear first second) third)) := by
      rw [form.vector_triple_product]
    _ = Vector3.sub
        (Vector3.scale
          (form.determinant * form.bilinear first third) second)
        (Vector3.scale
          (form.determinant * form.bilinear first second) third) := by
      ext <;> unfold Vector3.scale Vector3.sub <;> ring1

/-- Left-nested adjugate cross identity. -/
theorem cliffordCross_left_triple (form : Form K)
    (first second third : Vector3 K) :
    form.cliffordCross (form.cliffordCross first second) third =
      Vector3.sub
        (Vector3.scale
          (form.determinant * form.bilinear first third) second)
        (Vector3.scale
          (form.determinant * form.bilinear second third) first) := by
  calc
    form.cliffordCross (form.cliffordCross first second) third =
      Vector3.neg
        (form.cliffordCross third (form.cliffordCross first second)) :=
      form.cliffordCross_anticomm _ _
    _ = Vector3.neg
        (Vector3.sub
          (Vector3.scale
            (form.determinant * form.bilinear third second) first)
          (Vector3.scale
            (form.determinant * form.bilinear third first) second)) := by
      rw [form.cliffordCross_vector_triple]
    _ = Vector3.sub
        (Vector3.scale
          (form.determinant * form.bilinear first third) second)
        (Vector3.scale
          (form.determinant * form.bilinear second third) first) := by
      rw [form.bilinear_comm third second, form.bilinear_comm third first]
      ext <;> unfold Vector3.neg Vector3.sub Vector3.scale <;> ring1

/-- Compute the form-relative skew action matrix from the retained adjugate.

Multiply the coordinate antisymmetric anchor matrix by the cached adjugate; row multiplication then gives the adjugate
cross with the axis. -/
def actionSkew (form : Form K) (vector : Vector3 K) : Matrix3
  K :=
  Matrix3.mul (Coordinates3.Antisymmetric.anchor vector) form.adjugate

open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
/-- Row multiplication by the retained skew action matrix computes the adjugate cross with its axis. -/
theorem rowMul_actionSkew (form : Form K) (axis vector :
  Vector3 K) :
    Matrix3.rowMul vector (form.actionSkew axis) =
      form.cliffordCross axis vector := by
  unfold Form.actionSkew Form.cliffordCross
  rw [← Matrix3.rowMul_mul, Coordinates3.Antisymmetric.rowMul_anchor]

/-- Quadratic relation for the skew action, derived from the vector triple
product rather than a coordinate determinant expansion. -/
theorem actionSkew_square (form : Form K) (axis : Vector3 K)
  :
    Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
      Matrix3.sub
        (Matrix3.scale form.determinant
          (Matrix3.outer (form.dual axis) axis))
        (Matrix3.scale (form.determinant * form.quadrance axis)
          Matrix3.identity) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [← Matrix3.rowMul_mul, form.rowMul_actionSkew,
    form.rowMul_actionSkew, form.cliffordCross_vector_triple,
    Matrix3.rowMul_sub, Matrix3.rowMul_scale, Matrix3.rowMul_outer,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    ← form.bilinear_eq_dot_dual,
    form.bilinear_comm axis vector]
  unfold Form.quadrance
  ext <;> unfold Vector3.sub Vector3.scale <;> ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

/-- The form-relative skew action matrix has zero trace. -/
theorem trace_actionSkew (form : Form K) (axis : Vector3 K) :
    Matrix3.trace (form.actionSkew axis) = 0 := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold Form.actionSkew
  rw [form.adjugate_spec]
  unfold Matrix3.trace Matrix3.mul Matrix3.adjugate Coordinates3.Antisymmetric.anchor
  rw [rt_tr, st_ts, sr_rs]
  ring1

/-- The principal trace of the skew action matrix is the form determinant times the axis quadrance. -/
theorem principalTrace_actionSkew (form : Form K)
    (axis : Vector3 K) :
    Matrix3.principalTrace (form.actionSkew axis) =
      form.determinant * form.quadrance axis := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold Form.actionSkew
  rw [form.adjugate_spec, form.determinant_spec]
  unfold Matrix3.principalTrace Matrix3.trace Matrix3.adjugate
    Matrix3.determinant Matrix3.mul Coordinates3.Antisymmetric.anchor Form.quadrance Form.bilinear
    Matrix3.rowMul Vector3.dot
  rw [rt_tr, st_ts, sr_rs]
  ring1

/-- The form-relative skew action matrix has zero determinant. -/
@[simp] theorem determinant_actionSkew (form : Form K)
    (axis : Vector3 K) :
    Matrix3.determinant (form.actionSkew axis) = 0 := by
  unfold Form.actionSkew
  rw [Matrix3.determinant_mul, Coordinates3.Antisymmetric.determinant_anchor, zero_mul]

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic in
/-- A form-relative skew matrix with zero square has zero axis when two is nonzero.

The supplied equality decision, cached nondegeneracy and coordinate outer-product identity rule out a nonzero
square-zero skew action. -/
theorem axis_eq_zero_of_actionSkew_square_eq_zero
  [DecidableEq K]
    (form : Form K) (axis : Vector3 K)
    (twoNonzero : (2 : K) ≠ 0)
    (squareZero :
      Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
        Matrix3.zero) :
    axis = Vector3.zero := open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in by
  have squareFormula := form.actionSkew_square axis
  rw [squareZero] at squareFormula
  have dualDot :
      (form.dual axis).t * axis.t +
          (form.dual axis).r * axis.r +
          (form.dual axis).s * axis.s =
        form.quadrance axis := by
    unfold Form.dual Form.quadrance Form.bilinear Matrix3.rowMul Vector3.dot
    ring1
  have ttFormula := congrArg Matrix3.tt squareFormula
  have rrFormula := congrArg Matrix3.rr squareFormula
  have ssFormula := congrArg Matrix3.ss squareFormula
  simp only [Matrix3.zero, Matrix3.sub, Matrix3.scale, Matrix3.outer,
    Matrix3.identity, mul_one] at ttFormula rrFormula ssFormula
  have ttTerm :
      form.determinant * ((form.dual axis).t * axis.t) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).t * axis.t) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).t * axis.t) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← ttFormula, add_zero]
  have rrTerm :
      form.determinant * ((form.dual axis).r * axis.r) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).r * axis.r) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).r * axis.r) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← rrFormula, add_zero]
  have ssTerm :
      form.determinant * ((form.dual axis).s * axis.s) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).s * axis.s) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).s * axis.s) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← ssFormula, add_zero]
  have twiceDetQuadranceZero :
      2 * (form.determinant * form.quadrance axis) = 0 := by
    calc
      2 * (form.determinant * form.quadrance axis) =
          3 * (form.determinant * form.quadrance axis) -
            form.determinant * form.quadrance axis := by
        ring1
      _ = (form.determinant * ((form.dual axis).t * axis.t) +
              form.determinant * ((form.dual axis).r * axis.r) +
              form.determinant * ((form.dual axis).s * axis.s)) -
            form.determinant * form.quadrance axis := by
        rw [ttTerm, rrTerm, ssTerm]
        ring1
      _ = form.determinant *
            ((form.dual axis).t * axis.t +
              (form.dual axis).r * axis.r +
              (form.dual axis).s * axis.s) -
            form.determinant * form.quadrance axis := by
        ring1
      _ = 0 := by rw [dualDot]; ring1
  have detQuadranceZero :
      form.determinant * form.quadrance axis = 0 :=
    scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
      twiceDetQuadranceZero
  have quadranceZero : form.quadrance axis = 0 :=
    scalar_eq_zero_of_nonzero_mul_eq_zero form.determinantNonzero
      detQuadranceZero
  have scaledOuterZero :
      Matrix3.scale form.determinant
          (Matrix3.outer (form.dual axis) axis) =
        Matrix3.zero := by
    have removed :
        Matrix3.scale (form.determinant * form.quadrance axis)
            Matrix3.identity = Matrix3.zero := by
      rewrite [quadranceZero]
      apply Matrix3.ext <;> unfold Matrix3.scale Matrix3.identity Matrix3.zero <;> ring1
    have subtractZero :
        Matrix3.sub
            (Matrix3.scale form.determinant
              (Matrix3.outer (form.dual axis) axis)) Matrix3.zero =
          Matrix3.scale form.determinant
            (Matrix3.outer (form.dual axis) axis) := by
      apply Matrix3.ext <;> unfold Matrix3.sub Matrix3.zero <;> ring1
    calc
      Matrix3.scale form.determinant (Matrix3.outer (form.dual axis) axis) =
          Matrix3.sub
            (Matrix3.scale form.determinant (Matrix3.outer (form.dual axis) axis))
            Matrix3.zero := subtractZero.symm
      _ = Matrix3.sub
          (Matrix3.scale form.determinant (Matrix3.outer (form.dual axis) axis))
          (Matrix3.scale (form.determinant * form.quadrance axis) Matrix3.identity) :=
        congrArg
          (Matrix3.sub (Matrix3.scale form.determinant
            (Matrix3.outer (form.dual axis) axis))) removed.symm
      _ = Matrix3.zero := squareFormula.symm
  have outerZero :
      Matrix3.outer (form.dual axis) axis = Matrix3.zero := by
    apply Matrix3.ext
    all_goals
      apply scalar_eq_zero_of_nonzero_mul_eq_zero form.determinantNonzero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.tt scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.tr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.ts scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rt scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rs scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.st scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.sr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.ss scaledOuterZero
  have dualZero : form.dual axis = Vector3.zero := by
    by_cases axisTZero : axis.t = 0
    · by_cases axisRZero : axis.r = 0
      · by_cases axisSZero : axis.s = 0
        · have axisZero : axis = Vector3.zero := by
            apply Vector3.ext
            · exact axisTZero
            · exact axisRZero
            · exact axisSZero
          rw [axisZero]
          ext <;> unfold Form.dual Matrix3.rowMul Vector3.zero <;> ring1
        · apply Vector3.ext
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.ts outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.rs outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.ss outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply Vector3.ext
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.tr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.rr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.sr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
    · apply Vector3.ext
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.tt outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.rt outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.st outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
  exact form.eq_zero_of_rowMul_matrix_eq_zero axis dualZero

open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
/-- A displayed matrix whose form-adjoint is its negative is encoded by the
form-relative skew coordinates.  If it also squares to zero, the
three-dimensional skew obstruction forces the matrix itself to vanish. -/
theorem
  matrix_eq_zero_of_mul_form_antisymmetric_of_square_eq_zero
    [DecidableEq K] (form : Form K) (matrix : Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0)
    (antisymmetric :
      Matrix3.IsAntisymmetric (Matrix3.mul matrix form.matrix))
    (squareZero : Matrix3.mul matrix matrix = Matrix3.zero) :
    matrix = Matrix3.zero := by
  let axis := Coordinates3.Antisymmetric.anchorVector (Matrix3.mul matrix form.matrix)
  have encodes :
      Coordinates3.Antisymmetric.anchor axis = Matrix3.mul matrix form.matrix :=
    Coordinates3.Antisymmetric.anchor_anchorVector_of_isAntisymmetric
      (Matrix3.mul matrix form.matrix) twoNonzero antisymmetric
  have actionScale :
      form.actionSkew axis = Matrix3.scale form.determinant matrix := by
    unfold Form.actionSkew
    rw [encodes]
    calc
      Matrix3.mul (Matrix3.mul matrix form.matrix) form.adjugate =
          Matrix3.mul matrix
            (Matrix3.mul form.matrix form.adjugate) :=
        Matrix3.mul_assoc matrix form.matrix form.adjugate
      _ = Matrix3.mul matrix
          (Matrix3.scale form.determinant Matrix3.identity) := by
        rw [form.matrix_mul_adjugate]
      _ = Matrix3.scale form.determinant
          (Matrix3.mul matrix Matrix3.identity) :=
        Matrix3.mul_scale_right form.determinant matrix Matrix3.identity
      _ = Matrix3.scale form.determinant matrix := by
        rw [Matrix3.mul_identity]
  have actionSquareZero :
      Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
        Matrix3.zero := by
    rw [actionScale, Matrix3.mul_scale_left,
      Matrix3.mul_scale_right, Matrix3.scale_scale, squareZero]
    ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have axisZero :=
    form.axis_eq_zero_of_actionSkew_square_eq_zero axis twoNonzero
      actionSquareZero
  have matrixFormZero :
      Matrix3.mul matrix form.matrix = Matrix3.zero := by
    calc
      Matrix3.mul matrix form.matrix = Coordinates3.Antisymmetric.anchor axis := encodes.symm
      _ = Coordinates3.Antisymmetric.anchor Vector3.zero := by rw [axisZero]
      _ = Matrix3.zero := by
        ext <;> unfold Coordinates3.Antisymmetric.anchor Vector3.zero Matrix3.zero <;> ring1
  calc
    matrix = Matrix3.mul matrix Matrix3.identity := by
      rw [Matrix3.mul_identity]
    _ = Matrix3.mul matrix
        (Matrix3.mul form.matrix form.inverse) := by
      rw [form.matrix_mul_inverse]
    _ = Matrix3.mul
        (Matrix3.mul matrix form.matrix) form.inverse :=
      (Matrix3.mul_assoc matrix form.matrix form.inverse).symm
    _ = Matrix3.mul Matrix3.zero form.inverse := by rw [matrixFormZero]
    _ = Matrix3.zero := by
      ext <;> unfold Matrix3.mul Matrix3.zero <;> ring1

/-- A bilinearly skew displayed action has an explicitly antisymmetric
matrix after multiplication by the displayed form matrix. -/
theorem mul_form_isAntisymmetric_of_bilinear_skew
    (form : Form K) (matrix : Matrix3 K)
    (skew : ∀ left right : Vector3 K,
      form.bilinear (Matrix3.rowMul left matrix) right =
        -form.bilinear left (Matrix3.rowMul right matrix)) :
    Matrix3.IsAntisymmetric (Matrix3.mul matrix form.matrix) := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold Matrix3.IsAntisymmetric
  apply Matrix3.ext
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector3 K) (⟨1, 0, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector3 K) (⟨1, 0, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector3 K) (⟨1, 0, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector3 K) (⟨0, 1, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector3 K) (⟨0, 1, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector3 K) (⟨0, 1, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector3 K) (⟨0, 0, 1⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector3 K) (⟨0, 0, 1⟩ : Vector3 K)
  · simpa [Form.bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector3.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector3 K) (⟨0, 0, 1⟩ : Vector3 K)

set_option genInjectivity false in
/-- A scalar and displayed vector representing the even Clifford algebra of the indexed form.

The determinant-scaled convention uses the retained form pairing and adjugate cross for multiplication; no quotient or
basis selection is stored. -/
@[ext]
structure EvenClifford (form : Form K) where
  /-- The retained scalar coordinate. -/ scalar : K
  /-- The retained three-coordinate vector part. -/ vector : Vector3 K

constructive_injectivity Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.EvenClifford

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- The Clifford identity has scalar coordinate one and zero vector. -/
def identity (form : Form K) : form.EvenClifford
  :=
  ⟨1, Vector3.zero⟩

/-- Embed a displayed vector as a Clifford representative with zero scalar coordinate. -/
def ofVector (form : Form K) (vector : Vector3 K)
  :
    form.EvenClifford :=
  ⟨0, vector⟩

/-- Conjugate a Clifford representative by negating its vector part. -/
def conjugate {form : Form K} (value :
  form.EvenClifford) :
    form.EvenClifford :=
  ⟨value.scalar, Vector3.neg value.vector⟩

/-- Compute the reduced norm in the determinant-scaled vector convention.

Add the scalar square to the retained form determinant times the vector quadrance. -/
def norm {form : Form K} (value :
  form.EvenClifford) : K :=
  value.scalar ^ 2 + form.determinant * form.quadrance value.vector

/-- Multiply both the scalar and vector coordinates by the displayed homogeneous factor. -/
def scale {form : Form K} (factor : K)
    (value : form.EvenClifford) : form.EvenClifford :=
  ⟨factor * value.scalar, Vector3.scale factor value.vector⟩

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Unit homogeneous scaling leaves the Clifford representative unchanged. -/
@[simp] theorem one_scale {form : Form K}
    (value : form.EvenClifford) : scale 1 value = value := by
  apply Form.EvenClifford.ext
  · unfold scale
    ring1
  · exact Vector3.one_scale value.vector

/-- Successive homogeneous scalings equal scaling by the product of their factors. -/
theorem scale_scale {form : Form K} (first second
  : K)
    (value : form.EvenClifford) :
    scale first (scale second value) = scale (first * second) value := by
  apply Form.EvenClifford.ext
  · unfold scale
    ring1
  · unfold scale
    rw [Vector3.scale_scale]

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Homogeneous scaling multiplies the reduced norm by the square of its factor. -/
theorem norm_scale {form : Form K} (factor : K)
    (value : form.EvenClifford) :
    norm (scale factor value) = factor ^ 2 * norm value := by
  unfold norm scale
  rw [form.quadrance_scale]
  ring1

/-- Conjugation preserves the reduced norm. -/
theorem norm_conjugate {form : Form K}
    (value : form.EvenClifford) : norm (conjugate value) = norm value := by
  unfold norm conjugate Form.quadrance Form.bilinear Matrix3.rowMul Vector3.dot Vector3.neg
  ring1

/-- The Clifford identity has reduced norm one. -/
@[simp] theorem norm_identity (form : Form K) :
    norm (identity form) = 1 := by
  unfold norm identity
  rw [form.quadrance_zero]
  ring1

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Compute the scalar coordinate of the even Clifford product.

Subtract the form determinant times the vector pairing from the product of the two scalar coordinates. -/
def productScalar (form : Form K) (leftScalar
  rightScalar : K)
    (leftVector rightVector : Vector3 K) : K :=
  leftScalar * rightScalar -
    form.determinant * form.bilinear leftVector rightVector

/-- Compute the vector coordinate of the even Clifford product.

Add the two scalar-vector cross terms and subtract the retained adjugate cross of the vector parts. -/
def productVector (form : Form K) (leftScalar
  rightScalar : K)
    (leftVector rightVector : Vector3 K) : Vector3 K :=
  Vector3.sub
    (Vector3.add
      (Vector3.scale leftScalar rightVector)
      (Vector3.scale rightScalar leftVector))
    (form.cliffordCross leftVector rightVector)

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
/-- Multiply two Clifford representatives using their displayed scalar and vector formulas.

The computation reuses the indexed form pairing and cached adjugate through its denominator-free cross. -/
def mul {form : Form K} (left right :
  form.EvenClifford) :
    form.EvenClifford :=
  ⟨productScalar form left.scalar right.scalar left.vector right.vector,
    productVector form left.scalar right.scalar left.vector right.vector⟩

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
/-- The representative product is bilinear under independent homogeneous
rescalings. -/
theorem mul_scale_both {form : Form K}
    (leftFactor rightFactor : K) (left right : form.EvenClifford) :
    mul (scale leftFactor left) (scale rightFactor right) =
      scale (leftFactor * rightFactor) (mul left right) := by
  apply Form.EvenClifford.ext
  · simp only [mul, productScalar, scale]
    rw [form.bilinear_scale_left, form.bilinear_scale_right]
    ring1
  · simp only [mul, productVector, scale]
    rw [form.cliffordCross_scale_left, form.cliffordCross_scale_right]
    ext <;> unfold Vector3.add Vector3.sub Vector3.scale <;> ring1

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Scaling the left Clifford factor scales the product by the same factor. -/
theorem mul_scale_left {form : Form K} (factor :
  K)
    (left right : form.EvenClifford) :
    mul (scale factor left) right = scale factor (mul left right) :=
      by
  calc
    mul (scale factor left) right =
        mul (scale factor left) (scale 1 right) := by rw [one_scale]
    _ = scale (factor * 1) (mul left right) :=
      mul_scale_both factor 1 left right
    _ = scale factor (mul left right) := by rw [mul_one]

/-- Scaling the right Clifford factor scales the product by the same factor. -/
theorem mul_scale_right {form : Form K} (factor :
  K)
    (left right : form.EvenClifford) :
    mul left (scale factor right) = scale factor (mul left right) :=
      by
  calc
    mul left (scale factor right) =
        mul (scale 1 left) (scale factor right) := by rw [one_scale]
    _ = scale (1 * factor) (mul left right) :=
      mul_scale_both 1 factor left right
    _ = scale factor (mul left right) := by rw [one_mul]

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
/-- Embedding a scaled vector equals scaling its pure Clifford representative. -/
theorem ofVector_scale (form : Form K) (factor :
  K)
    (vector : Vector3 K) :
    ofVector form (Vector3.scale factor vector) =
      scale factor (ofVector form vector) := by
  apply Form.EvenClifford.ext
  · unfold ofVector scale
    ring1
  · rfl

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
open Purelib.Algebra.Quadratic.Ternary.Basic in
/-- Cancel a displayed nonzero homogeneous factor from even Clifford
coordinates. -/
theorem eq_of_scale_eq_scale {form : Form K}
  (factor : K)
    (factorNonzero : factor ≠ 0) {left right : form.EvenClifford}
    (equal : scale factor left = scale factor right) : left = right := open
      Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in by
  apply Form.EvenClifford.ext
  · apply TernaryForm.scalar_eq_of_nonzero_mul_eq_mul factorNonzero
    exact congrArg Form.EvenClifford.scalar equal
  · apply Vector3.ext
    · apply TernaryForm.scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.t) equal
    · apply TernaryForm.scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.r) equal
    · apply TernaryForm.scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.s) equal

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Expand the pairing of a Clifford product vector with a test vector.

The expansion is the sum of its two scalar-vector pairings minus the adjugate-cross pairing. -/
theorem bilinear_productVector (form : Form K)
    (leftScalar rightScalar : K) (leftVector rightVector test : Vector3 K) :
    form.bilinear
        (productVector form leftScalar rightScalar leftVector rightVector)
        test =
      leftScalar * form.bilinear rightVector test +
        rightScalar * form.bilinear leftVector test -
          form.bilinear (form.cliffordCross leftVector rightVector) test := by
  unfold productVector
  rw [form.bilinear_sub_left, form.bilinear_add_left,
    form.bilinear_scale_left, form.bilinear_scale_left]

/-- The vector coordinate has the norm expansion needed for reduced-norm
multiplicativity. -/
theorem quadrance_productVector (form : Form K)
    (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K) :
    form.quadrance
        (productVector form leftScalar rightScalar leftVector rightVector) =
      leftScalar ^ 2 * form.quadrance rightVector +
        2 * leftScalar * rightScalar * form.bilinear leftVector rightVector +
        rightScalar ^ 2 * form.quadrance leftVector +
        form.determinant *
          (form.quadrance leftVector * form.quadrance rightVector -
            form.bilinear leftVector rightVector ^ 2) := by
  have leftCross :
      form.bilinear leftVector
          (form.cliffordCross leftVector rightVector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left leftVector rightVector
  have rightCross :
      form.bilinear rightVector
          (form.cliffordCross leftVector rightVector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right leftVector rightVector
  unfold productVector
  rw [form.quadrance_sub, form.quadrance_add,
    form.quadrance_scale, form.quadrance_scale,
    form.bilinear_add_left, form.bilinear_scale_left,
    form.bilinear_scale_left, rightCross,
    form.bilinear_scale_left, leftCross,
    form.bilinear_scale_right,
    form.bilinear_comm rightVector leftVector,
    form.quadrance_cliffordCross]
  ring1

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- The Clifford identity is an exact left multiplicative identity. -/
@[simp] theorem identity_mul {form : Form K}
    (value : form.EvenClifford) : mul (identity form) value = value := by
  apply Form.EvenClifford.ext
  · unfold mul identity productScalar
    rw [form.bilinear_zero_left]
    ring1
  · ext <;> unfold mul identity productVector Vector3.add Vector3.sub
      Vector3.scale
      Vector3.zero Form.cliffordCross Vector3.cross Matrix3.rowMul <;> ring1

/-- The Clifford identity is an exact right multiplicative identity. -/
@[simp] theorem mul_identity {form : Form K}
    (value : form.EvenClifford) : mul value (identity form) = value := by
  apply Form.EvenClifford.ext
  · unfold mul identity productScalar
    rw [form.bilinear_zero_right]
    ring1
  · ext <;> unfold mul identity productVector Vector3.add Vector3.sub
      Vector3.scale
      Vector3.zero Form.cliffordCross Vector3.cross Matrix3.rowMul <;> ring1

/-- Multiplication is associative by a direct finite coordinate proof. -/
theorem mul_assoc {form : Form K}
    (first second third : form.EvenClifford) :
    mul (mul first second) third = mul first (mul second third) :=
      by
  apply Form.EvenClifford.ext
  · simp only [mul, productScalar]
    rw [bilinear_productVector]
    rw [form.bilinear_comm first.vector
      (productVector form second.scalar third.scalar
        second.vector third.vector)]
    rw [bilinear_productVector]
    rw [form.bilinear_comm third.vector first.vector,
      form.bilinear_comm second.vector first.vector,
      form.bilinear_cliffordCross_cyclic,
      form.bilinear_comm first.vector
        (form.cliffordCross second.vector third.vector)]
    ring1
  · simp only [mul, productScalar, productVector]
    simp only [form.cliffordCross_sub_left,
      form.cliffordCross_sub_right,
      form.cliffordCross_add_left,
      form.cliffordCross_add_right,
      form.cliffordCross_scale_left,
      form.cliffordCross_scale_right]
    rw [form.cliffordCross_left_triple,
      form.cliffordCross_vector_triple]
    ext <;> unfold Vector3.add Vector3.sub Vector3.scale <;> ring1

/-- Clifford conjugation reverses the explicit product. -/
theorem conjugate_mul_reverse {form : Form K}
    (left right : form.EvenClifford) :
    (conjugate (mul left right)) = mul (conjugate right)
      (conjugate left) := by
  apply Form.EvenClifford.ext
  · simp only [conjugate, mul, productScalar]
    rw [form.bilinear_neg_left, form.bilinear_neg_right,
      form.bilinear_comm right.vector left.vector]
    ring1
  · simp only [conjugate, mul, productVector]
    rw [form.cliffordCross_neg_left, form.cliffordCross_neg_right,
      form.cliffordCross_anticomm right.vector left.vector]
    ext <;> unfold Vector3.add Vector3.sub Vector3.scale Vector3.neg <;> ring1

/-- A Clifford value times its conjugate has its reduced norm as scalar coordinate and zero vector. -/
theorem mul_conjugate {form : Form K}
    (value : form.EvenClifford) :
    mul value (conjugate value) =
      ⟨(norm value), Vector3.zero⟩ := by
  apply Form.EvenClifford.ext
  · unfold mul productScalar conjugate norm Form.quadrance
      Form.bilinear
      Matrix3.rowMul Vector3.dot Vector3.neg
    ring1
  · ext <;> unfold mul productVector conjugate Form.cliffordCross Matrix3.rowMul
      Vector3.cross Vector3.add Vector3.sub Vector3.scale Vector3.neg Vector3.zero <;>
      ring1

/-- A Clifford conjugate times its original value has the reduced norm as scalar coordinate and zero vector. -/
theorem conjugate_mul {form : Form K}
    (value : form.EvenClifford) :
    mul (conjugate value) value =
      ⟨(norm value), Vector3.zero⟩ := by
  apply Form.EvenClifford.ext
  · unfold mul productScalar conjugate norm Form.quadrance
      Form.bilinear
      Matrix3.rowMul Vector3.dot Vector3.neg
    ring1
  · ext <;> unfold mul productVector conjugate Form.cliffordCross Matrix3.rowMul
      Vector3.cross Vector3.add Vector3.sub Vector3.scale Vector3.neg Vector3.zero <;>
      ring1

/-- A value times its conjugate is the identity scaled by its reduced norm. -/
theorem mul_conjugate_eq_scale_identity {form :
  Form K}
    (value : form.EvenClifford) :
    mul value (conjugate value) = scale (norm value)
      (identity form) := by
  rw [mul_conjugate]
  apply Form.EvenClifford.ext
  · unfold scale identity
    ring1
  · ext <;> unfold scale identity Vector3.scale Vector3.zero <;> ring1

/-- A conjugate times its original value is the identity scaled by its reduced norm. -/
theorem conjugate_mul_eq_scale_identity {form :
  Form K}
    (value : form.EvenClifford) :
    mul (conjugate value) value = scale (norm value)
      (identity form) := by
  rw [conjugate_mul]
  apply Form.EvenClifford.ext
  · unfold scale identity
    ring1
  · ext <;> unfold scale identity Vector3.scale Vector3.zero <;> ring1

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Scale the conjugate by the inverse of the original reduced norm.

The supplied nonzero-norm certificate makes the displayed representative a two-sided multiplicative inverse. -/
def inverse {form : Form K} (value :
  form.EvenClifford)
    (_normNonzero : (norm value) ≠ 0) : form.EvenClifford :=
  scale (norm value)⁻¹ (conjugate value)

/-- A Clifford representative times its certified inverse is the identity. -/
@[simp] theorem mul_inverse {form : Form K}
    (value : form.EvenClifford) (normNonzero : (norm value) ≠ 0) :
    mul value (inverse value normNonzero) = identity form := by
  have cancel := ExplicitField.mul_inv_cancel (norm value) normNonzero
  have reverseCancel : (norm value)⁻¹ * (norm value) = 1 := by
    calc
      (norm value)⁻¹ * (norm value) = (norm value) * (norm value)⁻¹
        := by ring1
      _ = 1 := cancel
  calc
    mul value (inverse value normNonzero) =
        mul (scale 1 value) (scale (norm value)⁻¹
          (conjugate value)) := by
      rw [one_scale]
      rfl
    _ = scale (1 * (norm value)⁻¹) (mul value (conjugate value)) :=
      mul_scale_both 1 (norm value)⁻¹ value (conjugate value)
    _ = scale (norm value)⁻¹
        (scale (norm value) (identity form)) := by
      rw [one_mul, mul_conjugate_eq_scale_identity]
    _ = scale ((norm value)⁻¹ * (norm value)) (identity form) := by
      rw [scale_scale]
    _ = identity form := by rw [reverseCancel, one_scale]

/-- The certified inverse times its original Clifford representative is the identity. -/
@[simp] theorem inverse_mul {form : Form K}
    (value : form.EvenClifford) (normNonzero : (norm value) ≠ 0) :
    mul (inverse value normNonzero) value = identity form := by
  have cancel := ExplicitField.mul_inv_cancel (norm value) normNonzero
  have reverseCancel : (norm value)⁻¹ * (norm value) = 1 := by
    calc
      (norm value)⁻¹ * (norm value) = (norm value) * (norm value)⁻¹
        := by ring1
      _ = 1 := cancel
  calc
    mul (inverse value normNonzero) value =
        mul (scale (norm value)⁻¹ (conjugate value))
          (scale 1 value) := by
      rw [one_scale]
      rfl
    _ = scale ((norm value)⁻¹ * 1) (mul (conjugate value) value) :=
      mul_scale_both (norm value)⁻¹ 1 (conjugate value) value
    _ = scale (norm value)⁻¹
        (scale (norm value) (identity form)) := by
      rw [mul_one, conjugate_mul_eq_scale_identity]
    _ = scale ((norm value)⁻¹ * (norm value)) (identity form) := by
      rw [scale_scale]
    _ = identity form := by rw [reverseCancel, one_scale]

/-- The reduced norm is multiplicative. -/
theorem norm_mul {form : Form K}
    (left right : form.EvenClifford) :
    norm (mul left right) = norm left * norm right := by
  simp only [norm, mul, productScalar]
  rw [quadrance_productVector]
  ring1

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
set_option genInjectivity false in
/-- An even Clifford representative with a certificate of nonzero reduced norm.

The original scalar and vector coordinates are retained through the nominal parent, and the certificate supports
executable inversion and normalized actions. -/
@[ext]
structure NonNullEvenClifford (form : Form K)
    extends form.EvenClifford where
  /-- The original even Clifford representative has nonzero reduced norm. -/ normNonzero : (EvenClifford.norm
    toEvenClifford) ≠ 0

constructive_injectivity Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.NonNullEvenClifford

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

/-- Explicit homogeneous rescaling with its cached non-null certificate. -/
def scale {form : Form K} (factor : K)
  (factorNonzero : factor ≠ 0)
    (value : form.NonNullEvenClifford) : form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.scale factor value.toEvenClifford
  normNonzero := by
    rw [EvenClifford.norm_scale]
    exact ExplicitField.mul_ne_zero
      (by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero factorNonzero factorNonzero)
      value.normNonzero

/-- Equality of represented projective Clifford points by an explicit
nonzero homogeneous scale. -/
def Equivalent {form : Form K}
    (left right : form.NonNullEvenClifford) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.toEvenClifford = EvenClifford.scale factor left.toEvenClifford

/-- Every non-null Clifford representative is projectively equivalent to itself using unit scale. -/
theorem equivalent_refl {form : Form K}
    (value : form.NonNullEvenClifford) : (Equivalent value) value := by
  exact ⟨1, form.one_ne_zero, (EvenClifford.one_scale _).symm⟩

/-- Reverse projective Clifford equivalence by inverting its supplied nonzero scale. -/
theorem equivalent_symm {form : Form K}
    {left right : form.NonNullEvenClifford}
    (equivalent : (Equivalent left) right) : (Equivalent right) left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.toEvenClifford =
        EvenClifford.scale 1 left.toEvenClifford := by
      rw [EvenClifford.one_scale]
    _ = EvenClifford.scale (factor⁻¹ * factor) left.toEvenClifford := by
      rw [reverseCancel]
    _ = EvenClifford.scale factor⁻¹
        (EvenClifford.scale factor left.toEvenClifford) := by
      rw [EvenClifford.scale_scale]
    _ = EvenClifford.scale factor⁻¹ right.toEvenClifford := by
      rw [← rightValue]

/-- Compose projective Clifford equivalences by multiplying their retained nonzero scales. -/
theorem equivalent_trans {form : Form K}
    {first second third : form.NonNullEvenClifford}
    (firstSecond : (Equivalent first) second)
    (secondThird : (Equivalent second) third) : (Equivalent first) third := by
  rcases firstSecond with
    ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with
    ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.toEvenClifford =
        EvenClifford.scale secondFactor second.toEvenClifford := thirdValue
    _ = EvenClifford.scale secondFactor
        (EvenClifford.scale firstFactor first.toEvenClifford) := by
      rw [secondValue]
    _ = EvenClifford.scale (secondFactor * firstFactor)
        first.toEvenClifford := EvenClifford.scale_scale _ _ _

/-- A nonzero homogeneous rescaling represents the same projective Clifford point. -/
theorem equivalent_scale {form : Form K}
  (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford) :
    (Equivalent value) (scale factor factorNonzero value) := by
  exact ⟨factor, factorNonzero, rfl⟩

/-- Total multiplication on representatives with nonzero reduced norm. -/
def mul {form : Form K} (left right :
  form.NonNullEvenClifford) :
    form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.mul left.toEvenClifford right.toEvenClifford
  normNonzero := by
    rw [EvenClifford.norm_mul]
    exact ExplicitField.mul_ne_zero left.normNonzero right.normNonzero

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

end

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm in
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
/-- Multiplication of non-null Clifford representatives is associative. -/
theorem mul_assoc {form : Form K}
    (first second third : form.NonNullEvenClifford) :
    mul (mul first second) third = mul first
      (mul second third) := by
  have raw := EvenClifford.mul_assoc first.toEvenClifford
    second.toEvenClifford third.toEvenClifford
  apply Form.NonNullEvenClifford.ext
  · exact congrArg Form.EvenClifford.scalar raw
  · exact congrArg Form.EvenClifford.vector raw

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

/-- Clifford multiplication respects projective equivalence in both inputs.

The product of the supplied nonzero scales witnesses the resulting equivalence. -/
theorem mul_respects_equivalent {form :
  Form K}
    {left left' right right' : form.NonNullEvenClifford}
    (leftEquivalent : (Equivalent left) left')
    (rightEquivalent : (Equivalent right) right') :
    (Equivalent (mul left right)) (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with
    ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change EvenClifford.mul left'.toEvenClifford right'.toEvenClifford =
    EvenClifford.scale (leftFactor * rightFactor)
      (EvenClifford.mul left.toEvenClifford right.toEvenClifford)
  rw [leftValue, rightValue, EvenClifford.mul_scale_both]

/-- The non-null Clifford identity representative. -/
def identity (form : Form K) :
  form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.identity form
  normNonzero := by
    rw [EvenClifford.norm_identity]
    exact form.one_ne_zero

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

end

section
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

/-- The non-null Clifford identity is an exact left multiplicative identity. -/
@[simp] theorem identity_mul {form : Form
  K}
    (value : form.NonNullEvenClifford) : mul (identity form) value = value := by
  have raw := EvenClifford.identity_mul value.toEvenClifford
  apply Form.NonNullEvenClifford.ext
  · exact congrArg Form.EvenClifford.scalar raw
  · exact congrArg Form.EvenClifford.vector raw

/-- The non-null Clifford identity is an exact right multiplicative identity. -/
@[simp] theorem mul_identity {form : Form
  K}
    (value : form.NonNullEvenClifford) : mul value (identity form) = value := by
  have raw := EvenClifford.mul_identity value.toEvenClifford
  apply Form.NonNullEvenClifford.ext
  · exact congrArg Form.EvenClifford.scalar raw
  · exact congrArg Form.EvenClifford.vector raw

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

end

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

/-- Conjugation preserves the non-null reduced-norm certificate. -/
def conjugate {form : Form K} (value :
  form.NonNullEvenClifford) :
    form.NonNullEvenClifford where
  toEvenClifford := (EvenClifford.conjugate value.toEvenClifford)
  normNonzero := by
    rw [EvenClifford.norm_conjugate]
    exact value.normNonzero

/-- A non-null Clifford value times its conjugate is projectively equivalent to the identity.

Its original nonzero reduced norm supplies the homogeneous factor. -/
theorem mul_conjugate_equivalent_identity
  {form : Form K}
    (value : form.NonNullEvenClifford) :
    (Equivalent (mul value (conjugate value)))
      (identity form) := by
  apply equivalent_symm
  refine ⟨(EvenClifford.norm value.toEvenClifford), value.normNonzero, ?_⟩
  exact EvenClifford.mul_conjugate_eq_scale_identity value.toEvenClifford

/-- A non-null Clifford conjugate times its original value is projectively equivalent to the identity.

Its original nonzero reduced norm supplies the homogeneous factor. -/
theorem conjugate_mul_equivalent_identity
  {form : Form K}
    (value : form.NonNullEvenClifford) :
    (Equivalent (mul (conjugate value) value))
      (identity form) := by
  apply equivalent_symm
  refine ⟨(EvenClifford.norm value.toEvenClifford), value.normNonzero, ?_⟩
  exact EvenClifford.conjugate_mul_eq_scale_identity value.toEvenClifford

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

end
end

end

end

public section

section

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

/-- Add scalar and vector coordinates in the original form-indexed Clifford algebra. -/
@[expose] def add {K : Type*} [ExplicitField K] {form : TernaryForm K}
    (left right : form.EvenClifford) : form.EvenClifford :=
  ⟨left.scalar + right.scalar, Vector3.add left.vector right.vector⟩

/-- Clifford multiplication distributes over addition in its right input. -/
theorem mul_add {K : Type*} [ExplicitField K] {form : TernaryForm K}
    (value left right : form.EvenClifford) : mul value (add left right) = add (mul value left) (mul value right) := by
  apply TernaryForm.EvenClifford.ext
  · dsimp only [mul, add, productScalar]
    rw [form.bilinear_add_right]
    ring1
  · dsimp only [mul, add, productVector]
    rw [form.cliffordCross_add_right]
    ext <;> dsimp only [Vector3.add, Vector3.sub, Vector3.scale] <;> ring1

/-- Clifford multiplication distributes over addition in its left input. -/
theorem add_mul {K : Type*} [ExplicitField K] {form : TernaryForm K}
    (left right value : form.EvenClifford) : mul (add left right) value = add (mul left value) (mul right value) := by
  apply TernaryForm.EvenClifford.ext
  · dsimp only [mul, add, productScalar]
    rw [form.bilinear_add_left]
    ring1
  · dsimp only [mul, add, productVector]
    rw [form.cliffordCross_add_left]
    ext <;> dsimp only [Vector3.add, Vector3.sub, Vector3.scale] <;> ring1

/-- A Clifford representative has a two-sided inverse exactly when its original reduced norm is nonzero.

A nonzero norm gives the conjugate divided by that norm as an explicit
inverse. Norm multiplicativity and the identity norm prove the converse.
-/
theorem invertible_iff_norm_ne_zero {K : Type*} [ExplicitField K] {form : TernaryForm K}
    (value : form.EvenClifford) :
    (∃ inverse : form.EvenClifford, mul value inverse = identity form ∧ mul inverse value = identity form) ↔
      norm value ≠ 0 := by
  constructor
  · rintro ⟨inverse, productIdentity, _⟩ normZero
    have productNorm := congrArg norm productIdentity
    rw [norm_mul, norm_identity, normZero, zero_mul] at productNorm
    exact form.one_ne_zero productNorm.symm
  · intro normNonzero
    exact ⟨inverse value normNonzero, mul_inverse value normNonzero, inverse_mul value normNonzero⟩

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford

end
