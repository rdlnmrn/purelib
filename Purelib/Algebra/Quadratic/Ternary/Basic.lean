module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.GroupWithZero.Basic

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open _root_.Purelib.LinearAlgebra.Coordinates3 (Matrix3)

open _root_.Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Constructive displayed ternary forms

This module begins the finite coordinate-algebra part of Problem 71.  A form
stores its displayed symmetric matrix together with cached determinant,
adjugate, and inverse data.  The certificates connect every cached value to
the canonical fixed-size matrix calculation, so downstream executable code
does not repeat those calculations or recover an inverse by choice.
-/

namespace Purelib.Algebra.Quadratic.Ternary.Basic

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A symmetric nondegenerate ternary form with retained matrix computations.

The displayed matrix, determinant, adjugate and inverse are executable data. Specification equalities and both
multiplication orders certify those exact cached values, so subsequent constructions can reuse them. -/
structure TernaryForm (K : Type*) [ExplicitField K] where
  /-- The retained displayed three-by-three form matrix. -/ matrix : Matrix3 K
  /-- Transposing the retained form matrix leaves it unchanged. -/ symmetric : Matrix3.transpose matrix = matrix
  /-- The cached scalar determinant of the retained matrix. -/ determinant : K
  /-- The cached determinant equals the coordinate determinant computation. -/ determinant_spec : determinant =
    Matrix3.determinant matrix
  /-- The retained determinant is nonzero, certifying nondegeneracy. -/ determinantNonzero : determinant ≠ 0
  /-- The cached adjugate of the retained matrix. -/ adjugate : Matrix3 K
  /-- The cached adjugate equals the coordinate adjugate computation. -/ adjugate_spec : adjugate = Matrix3.adjugate
    matrix
  /-- The matrix times its cached adjugate is the determinant-scaled identity. -/ matrix_mul_adjugate :
    Matrix3.mul matrix adjugate =
      Matrix3.scale determinant Matrix3.identity
  /-- The cached adjugate times the matrix is the determinant-scaled identity. -/ adjugate_mul_matrix :
    Matrix3.mul adjugate matrix =
      Matrix3.scale determinant Matrix3.identity
  /-- The cached inverse of the retained matrix. -/ inverse : Matrix3 K
  /-- The cached inverse equals the certified coordinate inverse computation. -/ inverse_spec : inverse =
    Matrix3.inverse matrix (by
    rw [← determinant_spec]
    exact determinantNonzero)
  /-- The cached inverse is a right inverse of the retained matrix. -/ matrix_mul_inverse : Matrix3.mul matrix inverse =
    Matrix3.identity
  /-- The cached inverse is a left inverse of the retained matrix. -/ inverse_mul_matrix : Matrix3.mul inverse matrix =
    Matrix3.identity

constructive_injectivity TernaryForm

namespace TernaryForm

/-- A zero product with a supplied nonzero scalar factor forces its other factor to be zero. -/
theorem cancel_scalar_of_nonzero_mul_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

section
open _root_.Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
/-- Construct a ternary form from a displayed symmetric matrix with nonzero determinant.

Compute and retain the determinant, adjugate and inverse, together with their defining equalities and two-sided
multiplication certificates. -/
def ofMatrix (matrix : Matrix3 K)
    (symmetric : Matrix3.transpose matrix = matrix)
    (determinantNonzero : Matrix3.determinant matrix ≠ 0) :
    Form K where
  matrix := matrix
  symmetric := symmetric
  determinant := Matrix3.determinant matrix
  determinant_spec := rfl
  determinantNonzero := determinantNonzero
  adjugate := Matrix3.adjugate matrix
  adjugate_spec := rfl
  matrix_mul_adjugate := Matrix3.mul_adjugate matrix
  adjugate_mul_matrix := Matrix3.adjugate_mul matrix
  inverse := Matrix3.inverse matrix determinantNonzero
  inverse_spec := rfl
  matrix_mul_inverse := Matrix3.mul_inverse matrix determinantNonzero
  inverse_mul_matrix := Matrix3.inverse_mul matrix determinantNonzero

/-- The cached determinant certifies nondegeneracy of the displayed matrix. -/
theorem matrix_determinant_nonzero (form : Form K) :
    Matrix3.determinant form.matrix ≠ 0 := by
  rw [← form.determinant_spec]
  exact form.determinantNonzero

/-- A displayed nondegenerate form can exist only over a nontrivial explicit
field. -/
theorem one_ne_zero (form : Form K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply form.determinantNonzero
  calc
    form.determinant = form.determinant * 1 := by rw [mul_one]
    _ = form.determinant * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- The cached inverse is tied to the canonical determinant-scaled adjugate
calculation. -/
theorem inverse_eq_scale_adjugate (form : Form K) :
    form.inverse =
      Matrix3.scale (1 / form.determinant) form.adjugate := by
  calc
    form.inverse = Matrix3.inverse form.matrix
        form.matrix_determinant_nonzero := form.inverse_spec
    _ = Matrix3.scale
        (1 / Matrix3.determinant form.matrix)
        (Matrix3.adjugate form.matrix) := rfl
    _ = Matrix3.scale (1 / form.determinant) form.adjugate := by
      rw [← form.determinant_spec, ← form.adjugate_spec]

/-- Evaluate the symmetric bilinear pairing defined by the retained form matrix.

The first row vector is multiplied by the matrix and paired with the second by the coordinate dot product. -/
def bilinear (form : Form K) (left right : Vector3 K) : K :=
  Vector3.dot (Matrix3.rowMul left form.matrix) right

/-- Evaluate the form on a vector paired with itself. -/
def quadrance (form : Form K) (vector : Vector3 K) : K :=
  form.bilinear vector vector

/-- A vector is null exactly when its quadrance in the retained form is zero. -/
def IsNull (form : Form K) (vector : Vector3 K) : Prop :=
  form.quadrance vector = 0

/-- Two vectors are perpendicular exactly when their retained form pairing is zero. -/
def Perpendicular (form : Form K) (left right : Vector3 K) :
  Prop :=
  form.bilinear left right = 0

/-- Add the scalar square to the vector quadrance in the retained ternary form. -/
def proportionNorm (form : Form K) (scalar : K)
    (vector : Vector3 K) : K :=
  scalar ^ 2 + form.quadrance vector

/-- The retained matrix symmetry makes the bilinear pairing symmetric. -/
theorem bilinear_comm (form : Form K) (left right : Vector3
  K) :
    form.bilinear left right = form.bilinear right left := by
  calc
    form.bilinear left right =
        Vector3.dot left
          (Matrix3.rowMul right (Matrix3.transpose form.matrix)) :=
      Matrix3.dot_rowMul_transpose left right form.matrix
    _ = Vector3.dot left (Matrix3.rowMul right form.matrix) := by
      rw [form.symmetric]
    _ = form.bilinear right left :=
      Vector3.dot_comm left (Matrix3.rowMul right form.matrix)

/-- The bilinear pairing respects addition in its left argument. -/
theorem bilinear_add_left (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear (Vector3.add first second) third =
      form.bilinear first third + form.bilinear second third := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.add
  ring1

/-- The bilinear pairing respects addition in its right argument. -/
theorem bilinear_add_right (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear first (Vector3.add second third) =
      form.bilinear first second + form.bilinear first third := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.add
  ring1

/-- The bilinear pairing respects subtraction in its left argument. -/
theorem bilinear_sub_left (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear (Vector3.sub first second) third =
      form.bilinear first third - form.bilinear second third := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.sub
  ring1

/-- The bilinear pairing respects subtraction in its right argument. -/
theorem bilinear_sub_right (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear first (Vector3.sub second third) =
      form.bilinear first second - form.bilinear first third := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.sub
  ring1

/-- The bilinear pairing respects scalar multiplication in its left argument. -/
theorem bilinear_scale_left (form : Form K) (scalar : K)
    (left right : Vector3 K) :
    form.bilinear (Vector3.scale scalar left) right =
      scalar * form.bilinear left right := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.scale
  ring1

/-- The bilinear pairing respects scalar multiplication in its right argument. -/
theorem bilinear_scale_right (form : Form K) (scalar : K)
    (left right : Vector3 K) :
    form.bilinear left (Vector3.scale scalar right) =
      scalar * form.bilinear left right := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.scale
  ring1

/-- The bilinear pairing respects negation in its left argument. -/
theorem bilinear_neg_left (form : Form K) (left right :
  Vector3 K) :
    form.bilinear (Vector3.neg left) right = -form.bilinear left right := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.neg
  ring1

/-- The bilinear pairing respects negation in its right argument. -/
theorem bilinear_neg_right (form : Form K) (left right :
  Vector3 K) :
    form.bilinear left (Vector3.neg right) = -form.bilinear left right := by
  rw [form.bilinear_comm, form.bilinear_neg_left,
    form.bilinear_comm right left]

/-- A zero left argument makes the bilinear pairing zero. -/
@[simp] theorem bilinear_zero_left (form : Form K)
    (vector : Vector3 K) : form.bilinear Vector3.zero vector = 0 := by
  unfold Form.bilinear Matrix3.rowMul Vector3.dot Vector3.zero
  ring1

/-- A zero right argument makes the bilinear pairing zero. -/
@[simp] theorem bilinear_zero_right (form : Form K)
    (vector : Vector3 K) : form.bilinear vector Vector3.zero = 0 := by
  rw [form.bilinear_comm, form.bilinear_zero_left]

/-- The zero vector has zero quadrance. -/
@[simp] theorem quadrance_zero (form : Form K) :
    form.quadrance Vector3.zero = 0 := by
  unfold Form.quadrance
  exact form.bilinear_zero_left Vector3.zero

/-- Negating a vector preserves its quadrance. -/
theorem quadrance_neg (form : Form K) (vector : Vector3 K) :
    form.quadrance (Vector3.neg vector) = form.quadrance vector := by
  unfold Form.quadrance
  rw [form.bilinear_neg_left, form.bilinear_neg_right, neg_neg]

/-- Scaling a vector multiplies its quadrance by the square of the scalar. -/
theorem quadrance_scale (form : Form K) (scalar : K)
    (vector : Vector3 K) :
    form.quadrance (Vector3.scale scalar vector) =
      scalar ^ 2 * form.quadrance vector := by
  unfold Form.quadrance
  rw [form.bilinear_scale_left, form.bilinear_scale_right]
  ring1

/-- Expand the quadrance of a sum into its two quadrances and twice the mixed pairing. -/
theorem quadrance_add (form : Form K) (left right : Vector3
  K) :
    form.quadrance (Vector3.add left right) =
      form.quadrance left + 2 * form.bilinear left right +
        form.quadrance right := by
  unfold Form.quadrance
  rw [form.bilinear_add_left, form.bilinear_add_right,
    form.bilinear_add_right, Form.bilinear_comm form right left]
  ring1

/-- Expand the quadrance of a difference into its two quadrances minus twice the mixed pairing. -/
theorem quadrance_sub (form : Form K) (left right : Vector3
  K) :
    form.quadrance (Vector3.sub left right) =
      form.quadrance left - 2 * form.bilinear left right +
        form.quadrance right := by
  unfold Form.quadrance
  rw [form.bilinear_sub_left, form.bilinear_sub_right,
    form.bilinear_sub_right, form.bilinear_comm right left]
  ring1

end

open _root_.Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
set_option genInjectivity false in
/-- A retained vector with nonzero quadrance in the indexed ternary form.

The vector is executable data, and the certificate concerns that exact vector and form. -/
structure NonNullVectorWitness (form : Form K) where
  /-- The retained executable vector. -/ value : Vector3 K
  /-- The retained vector has nonzero quadrance in the indexed form. -/ nonNull : form.quadrance value ≠ 0

constructive_injectivity NonNullVectorWitness

section
open _root_.Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
/-- Every displayed nondegenerate ternary form in characteristic different
from two has an executable non-null vector.  The selector tests the three
coordinate rows and their three pairwise sums; if all six quadrances vanished,
symmetry and polarization would force every matrix entry, hence the cached
determinant, to vanish. -/
def nonNullVectorWitness [DecidableEq K] (form : Form K)
    (twoNonzero : (2 : K) ≠ 0) : Form.NonNullVectorWitness form := by
  let basisT : Vector3 K := ⟨1, 0, 0⟩
  let basisR : Vector3 K := ⟨0, 1, 0⟩
  let basisS : Vector3 K := ⟨0, 0, 1⟩
  let sumTR : Vector3 K := Vector3.add basisT basisR
  let sumTS : Vector3 K := Vector3.add basisT basisS
  let sumRS : Vector3 K := Vector3.add basisR basisS
  by_cases basisTZero : form.quadrance basisT = 0
  · by_cases basisRZero : form.quadrance basisR = 0
    · by_cases basisSZero : form.quadrance basisS = 0
      · by_cases sumTRZero : form.quadrance sumTR = 0
        · by_cases sumTSZero : form.quadrance sumTS = 0
          · by_cases sumRSZero : form.quadrance sumRS = 0
            · have ttZero : form.matrix.tt = 0 := by
                simpa [basisT, Form.quadrance, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using basisTZero
              have rrZero : form.matrix.rr = 0 := by
                simpa [basisR, Form.quadrance, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using basisRZero
              have ssZero : form.matrix.ss = 0 := by
                simpa [basisS, Form.quadrance, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using basisSZero
              have twiceTR :
                  2 * form.bilinear basisT basisR = 0 := by
                have addition := form.quadrance_add basisT basisR
                change form.quadrance sumTR = _ at addition
                rw [sumTRZero, basisTZero, basisRZero] at addition
                calc
                  2 * form.bilinear basisT basisR =
                      0 + 2 * form.bilinear basisT basisR + 0 := by ring1
                  _ = 0 := addition.symm
              have twiceTS :
                  2 * form.bilinear basisT basisS = 0 := by
                have addition := form.quadrance_add basisT basisS
                change form.quadrance sumTS = _ at addition
                rw [sumTSZero, basisTZero, basisSZero] at addition
                calc
                  2 * form.bilinear basisT basisS =
                      0 + 2 * form.bilinear basisT basisS + 0 := by ring1
                  _ = 0 := addition.symm
              have twiceRS :
                  2 * form.bilinear basisR basisS = 0 := by
                have addition := form.quadrance_add basisR basisS
                change form.quadrance sumRS = _ at addition
                rw [sumRSZero, basisRZero, basisSZero] at addition
                calc
                  2 * form.bilinear basisR basisS =
                      0 + 2 * form.bilinear basisR basisS + 0 := by ring1
                  _ = 0 := addition.symm
              have trZero : form.matrix.tr = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                simpa [basisT, basisR, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using twiceTR
              have tsZero : form.matrix.ts = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                simpa [basisT, basisS, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using twiceTS
              have rsZero : form.matrix.rs = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                simpa [basisR, basisS, Form.bilinear, Matrix3.rowMul,
                  Vector3.dot] using twiceRS
              have rt_tr : form.matrix.rt = form.matrix.tr :=
                congrArg Matrix3.tr form.symmetric
              have st_ts : form.matrix.st = form.matrix.ts :=
                congrArg Matrix3.ts form.symmetric
              have sr_rs : form.matrix.sr = form.matrix.rs :=
                congrArg Matrix3.rs form.symmetric
              have determinantZero : form.determinant = 0 := by
                rw [form.determinant_spec]
                unfold Matrix3.determinant
                rw [ttZero, trZero, tsZero, rt_tr, rrZero, rsZero,
                  st_ts, sr_rs, ssZero]
                ring1
              exact (form.determinantNonzero determinantZero).elim
            · exact ⟨sumRS, sumRSZero⟩
          · exact ⟨sumTS, sumTSZero⟩
        · exact ⟨sumTR, sumTRZero⟩
      · exact ⟨basisS, basisSZero⟩
    · exact ⟨basisR, basisRZero⟩
  · exact ⟨basisT, basisTZero⟩

/-- Perpendicularity in the retained symmetric form is symmetric. -/
theorem perpendicular_comm (form : Form K) (left right :
  Vector3 K) :
    form.Perpendicular left right ↔ form.Perpendicular right left := by
  unfold Form.Perpendicular
  rw [form.bilinear_comm]

/-- Scaling the left vector preserves perpendicularity in the retained form. -/
theorem perpendicular_scale_left (form : Form K) (scalar : K)
    (left right : Vector3 K) (perpendicular : form.Perpendicular left right) :
    form.Perpendicular (Vector3.scale scalar left) right := by
  unfold Form.Perpendicular at perpendicular ⊢
  rw [form.bilinear_scale_left, perpendicular, mul_zero]

/-- Scaling the right vector preserves perpendicularity in the retained form. -/
theorem perpendicular_scale_right (form : Form K) (scalar :
  K)
    (left right : Vector3 K) (perpendicular : form.Perpendicular left right) :
    form.Perpendicular left (Vector3.scale scalar right) := by
  unfold Form.Perpendicular at perpendicular ⊢
  rw [form.bilinear_scale_right, perpendicular, mul_zero]

/-- Every scalar multiple of a null vector remains null. -/
theorem isNull_scale (form : Form K) (scalar : K)
    (vector : Vector3 K) (null : form.IsNull vector) :
    form.IsNull (Vector3.scale scalar vector) := by
  unfold Form.IsNull at null ⊢
  rw [form.quadrance_scale, null, mul_zero]

/-- Simultaneously scaling the scalar and vector coordinates multiplies the
projective norm by the square of the displayed scale. -/
theorem proportionNorm_scale (form : Form K) (factor scalar :
  K)
    (vector : Vector3 K) :
    form.proportionNorm (factor * scalar) (Vector3.scale factor vector) =
      factor ^ 2 * form.proportionNorm scalar vector := by
  unfold Form.proportionNorm
  rw [form.quadrance_scale]
  ring1

/-- The cached inverse makes matrix nondegeneracy executable: a vector killed
by the form matrix is the zero vector. -/
theorem eq_zero_of_rowMul_matrix_eq_zero (form : Form K)
    (vector : Vector3 K)
    (annihilated : Matrix3.rowMul vector form.matrix = Vector3.zero) :
    vector = Vector3.zero := by
  calc
    vector = Matrix3.rowMul vector Matrix3.identity := by
      rw [Matrix3.rowMul_identity]
    _ = Matrix3.rowMul vector
        (Matrix3.mul form.matrix form.inverse) := by
      rw [form.matrix_mul_inverse]
    _ = Matrix3.rowMul
        (Matrix3.rowMul vector form.matrix) form.inverse := by
      rw [Matrix3.rowMul_mul]
    _ = Matrix3.rowMul Vector3.zero form.inverse := by rw [annihilated]
    _ = Vector3.zero := by
      ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1

/-- Right multiplication by the displayed form matrix is injective, with the
cached inverse providing the explicit cancellation path. -/
theorem rowMul_matrix_injective (form : Form K)
    {left right : Vector3 K}
    (equal : Matrix3.rowMul left form.matrix =
      Matrix3.rowMul right form.matrix) :
    left = right := by
  calc
    left = Matrix3.rowMul
        (Matrix3.rowMul left form.matrix) form.inverse := by
      rw [Matrix3.rowMul_mul, form.matrix_mul_inverse,
        Matrix3.rowMul_identity]
    _ = Matrix3.rowMul
        (Matrix3.rowMul right form.matrix) form.inverse := by rw [equal]
    _ = right := by
      rw [Matrix3.rowMul_mul, form.matrix_mul_inverse,
        Matrix3.rowMul_identity]

/-- Nondegeneracy in bilinear form: equality against the three displayed
coordinate tests determines the source vector. -/
theorem eq_of_bilinear_eq (form : Form K) {left right :
  Vector3 K}
    (equal : ∀ test : Vector3 K,
      form.bilinear left test = form.bilinear right test) :
    left = right := by
  apply form.rowMul_matrix_injective
  apply Vector3.ext
  · simpa [Form.bilinear, Vector3.dot] using
      equal (⟨1, 0, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Vector3.dot] using
      equal (⟨0, 1, 0⟩ : Vector3 K)
  · simpa [Form.bilinear, Vector3.dot] using
      equal (⟨0, 0, 1⟩ : Vector3 K)

/-- Subtract the retained axis component from the quadrance-scaled test vector.

This denominator-free formula is perpendicular to the axis for every input; a non-null axis is needed only when
recovering a normalized projection. -/
def perpendicularProjection (form : Form K) (axis test :
  Vector3 K) :
    Vector3 K :=
  Vector3.sub
    (Vector3.scale (form.quadrance axis) test)
    (Vector3.scale (form.bilinear test axis) axis)

/-- The denominator-free projection is perpendicular to its retained axis. -/
theorem perpendicularProjection_perpendicular (form : Form K)
    (axis test : Vector3 K) :
    form.Perpendicular (form.perpendicularProjection axis test) axis := by
  unfold Form.Perpendicular Form.perpendicularProjection
  rw [form.bilinear_sub_left, form.bilinear_scale_left,
    form.bilinear_scale_left]
  change form.quadrance axis * form.bilinear test axis -
    form.bilinear test axis * form.quadrance axis = 0
  ring1

/-- The denominator-free projection preserves addition of test vectors. -/
theorem perpendicularProjection_add (form : Form K)
    (axis first second : Vector3 K) :
    form.perpendicularProjection axis (Vector3.add first second) =
      Vector3.add (form.perpendicularProjection axis first)
        (form.perpendicularProjection axis second) := by
  unfold Form.perpendicularProjection
  rw [form.bilinear_add_left]
  ext <;> unfold Vector3.add Vector3.sub Vector3.scale <;> ring1

/-- The cleared projection reconstructs the quadrance-scaled test vector
after its displayed axis component is restored. -/
theorem perpendicularProjection_reconstruct (form : Form K)
    (axis test : Vector3 K) :
    Vector3.add (form.perpendicularProjection axis test)
        (Vector3.scale (form.bilinear test axis) axis) =
      Vector3.scale (form.quadrance axis) test := by
  ext <;> unfold Form.perpendicularProjection Vector3.add Vector3.sub Vector3.scale <;>
    ring1

/-- Coordinate expansion of the cleared projection. -/
theorem perpendicularProjection_coordinateExpansion
    (form : Form K) (axis test : Vector3 K) :
    form.perpendicularProjection axis test =
      Vector3.add
        (Vector3.add
          (Vector3.scale test.t
            (form.perpendicularProjection axis (⟨1, 0, 0⟩ : Vector3 K)))
          (Vector3.scale test.r
            (form.perpendicularProjection axis (⟨0, 1, 0⟩ : Vector3 K))))
        (Vector3.scale test.s
          (form.perpendicularProjection axis (⟨0, 0, 1⟩ : Vector3 K))) := by
  ext <;> unfold Form.perpendicularProjection Form.quadrance Form.bilinear Matrix3.rowMul
    Vector3.dot Vector3.add Vector3.sub Vector3.scale <;> ring1

end

open _root_.Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form in
set_option genInjectivity false in
/-- A retained non-null vector perpendicular to the indexed axis.

Both the nonzero-quadrance and perpendicularity certificates refer to the original ternary form and displayed axis. -/
structure PerpendicularNonNullVectorWitness (form : Form K)
    (axis : Vector3 K) where
  /-- The retained executable vector. -/ value : Vector3 K
  /-- The retained vector is perpendicular to the original indexed axis. -/ perpendicular : form.Perpendicular value
    axis
  /-- The retained vector has nonzero quadrance in the indexed form. -/ nonNull : form.quadrance value ≠ 0

constructive_injectivity PerpendicularNonNullVectorWitness

open _root_.Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
/-- Select a non-null perpendicular vector by testing the cleared projections
of the three coordinate rows and their three pairwise sums.  The proof that
the six candidates cannot all be null uses only polarization, the explicit
coordinate expansion, and nondegeneracy. -/
def perpendicularNonNullVectorWitness [DecidableEq K]
    (form : Form K) (axis : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Form.PerpendicularNonNullVectorWitness form axis := by
  let basisT : Vector3 K := ⟨1, 0, 0⟩
  let basisR : Vector3 K := ⟨0, 1, 0⟩
  let basisS : Vector3 K := ⟨0, 0, 1⟩
  let projectedT := form.perpendicularProjection axis basisT
  let projectedR := form.perpendicularProjection axis basisR
  let projectedS := form.perpendicularProjection axis basisS
  let sumTR := Vector3.add projectedT projectedR
  let sumTS := Vector3.add projectedT projectedS
  let sumRS := Vector3.add projectedR projectedS
  have projectedTPerpendicular : form.Perpendicular projectedT axis :=
    form.perpendicularProjection_perpendicular axis basisT
  have projectedRPerpendicular : form.Perpendicular projectedR axis :=
    form.perpendicularProjection_perpendicular axis basisR
  have projectedSPerpendicular : form.Perpendicular projectedS axis :=
    form.perpendicularProjection_perpendicular axis basisS
  have sumTRPerpendicular : form.Perpendicular sumTR axis := by
    unfold sumTR Form.Perpendicular
    rw [form.bilinear_add_left, projectedTPerpendicular,
      projectedRPerpendicular, add_zero]
  have sumTSPerpendicular : form.Perpendicular sumTS axis := by
    unfold sumTS Form.Perpendicular
    rw [form.bilinear_add_left, projectedTPerpendicular,
      projectedSPerpendicular, add_zero]
  have sumRSPerpendicular : form.Perpendicular sumRS axis := by
    unfold sumRS Form.Perpendicular
    rw [form.bilinear_add_left, projectedRPerpendicular,
      projectedSPerpendicular, add_zero]
  by_cases projectedTZero : form.quadrance projectedT = 0
  · by_cases projectedRZero : form.quadrance projectedR = 0
    · by_cases projectedSZero : form.quadrance projectedS = 0
      · by_cases sumTRZero : form.quadrance sumTR = 0
        · by_cases sumTSZero : form.quadrance sumTS = 0
          · by_cases sumRSZero : form.quadrance sumRS = 0
            · have pairingTR : form.bilinear projectedT projectedR = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add projectedT projectedR
                change form.quadrance sumTR = _ at addition
                rw [sumTRZero, projectedTZero, projectedRZero] at addition
                calc
                  2 * form.bilinear projectedT projectedR =
                      0 + 2 * form.bilinear projectedT projectedR + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have pairingTS : form.bilinear projectedT projectedS = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add projectedT projectedS
                change form.quadrance sumTS = _ at addition
                rw [sumTSZero, projectedTZero, projectedSZero] at addition
                calc
                  2 * form.bilinear projectedT projectedS =
                      0 + 2 * form.bilinear projectedT projectedS + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have pairingRS : form.bilinear projectedR projectedS = 0 := by
                apply Form.cancel_scalar_of_nonzero_mul_zero twoNonzero
                have addition := form.quadrance_add projectedR projectedS
                change form.quadrance sumRS = _ at addition
                rw [sumRSZero, projectedRZero, projectedSZero] at addition
                calc
                  2 * form.bilinear projectedR projectedS =
                      0 + 2 * form.bilinear projectedR projectedS + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have projectionZero
                  (projected : Vector3 K)
                  (perpendicular : form.Perpendicular projected axis)
                  (pairT : form.bilinear projected projectedT = 0)
                  (pairR : form.bilinear projected projectedR = 0)
                  (pairS : form.bilinear projected projectedS = 0) :
                  projected = Vector3.zero := by
                apply form.eq_of_bilinear_eq
                intro test
                rw [form.bilinear_zero_left]
                apply Form.cancel_scalar_of_nonzero_mul_zero axisNonNull
                have projectedExpansion :
                    form.bilinear projected
                      (form.perpendicularProjection axis test) = 0 := by
                  rw [form.perpendicularProjection_coordinateExpansion,
                    form.bilinear_add_right, form.bilinear_add_right,
                    form.bilinear_scale_right, form.bilinear_scale_right,
                    form.bilinear_scale_right, pairT, pairR, pairS]
                  ring1
                unfold Form.Perpendicular at perpendicular
                calc
                  form.quadrance axis * form.bilinear projected test =
                      form.bilinear projected
                        (Vector3.scale (form.quadrance axis) test) :=
                    (form.bilinear_scale_right
                      (form.quadrance axis) projected test).symm
                  _ = form.bilinear projected
                      (Vector3.add (form.perpendicularProjection axis test)
                        (Vector3.scale (form.bilinear test axis) axis)) := by
                    rw [form.perpendicularProjection_reconstruct]
                  _ = form.bilinear projected
                        (form.perpendicularProjection axis test) +
                      form.bilinear projected
                        (Vector3.scale (form.bilinear test axis) axis) :=
                    form.bilinear_add_right projected _ _
                  _ = 0 := by
                    rw [projectedExpansion, form.bilinear_scale_right,
                      perpendicular, mul_zero, add_zero]
              have projectedTIsZero : projectedT = Vector3.zero := by
                apply projectionZero projectedT projectedTPerpendicular
                · exact projectedTZero
                · exact pairingTR
                · exact pairingTS
              have projectedRIsZero : projectedR = Vector3.zero := by
                apply projectionZero projectedR projectedRPerpendicular
                · rw [form.bilinear_comm]
                  exact pairingTR
                · exact projectedRZero
                · exact pairingRS
              have projectedSIsZero : projectedS = Vector3.zero := by
                apply projectionZero projectedS projectedSPerpendicular
                · rw [form.bilinear_comm]
                  exact pairingTS
                · rw [form.bilinear_comm]
                  exact pairingRS
                · exact projectedSZero
              have scaledT :
                  Vector3.scale (form.quadrance axis) basisT =
                    Vector3.scale (form.bilinear basisT axis) axis := by
                calc
                  Vector3.scale (form.quadrance axis) basisT =
                      Vector3.add projectedT
                        (Vector3.scale (form.bilinear basisT axis) axis) :=
                    (form.perpendicularProjection_reconstruct
                      axis basisT).symm
                  _ = Vector3.scale (form.bilinear basisT axis) axis := by
                    rw [projectedTIsZero, Vector3.zero_add]
              have scaledR :
                  Vector3.scale (form.quadrance axis) basisR =
                    Vector3.scale (form.bilinear basisR axis) axis := by
                calc
                  Vector3.scale (form.quadrance axis) basisR =
                      Vector3.add projectedR
                        (Vector3.scale (form.bilinear basisR axis) axis) :=
                    (form.perpendicularProjection_reconstruct
                      axis basisR).symm
                  _ = Vector3.scale (form.bilinear basisR axis) axis := by
                    rw [projectedRIsZero, Vector3.zero_add]
              have crossed := congrArg₂ Vector3.cross scaledT scaledR
              have leftCross :
                  Vector3.cross
                      (Vector3.scale (form.quadrance axis) basisT)
                      (Vector3.scale (form.quadrance axis) basisR) =
                    Vector3.scale (form.quadrance axis * form.quadrance axis)
                      basisS := by
                ext <;> unfold basisT basisR basisS Vector3.cross Vector3.scale <;>
                  ring1
              have rightCross :
                  Vector3.cross
                      (Vector3.scale (form.bilinear basisT axis) axis)
                      (Vector3.scale (form.bilinear basisR axis) axis) =
                    Vector3.zero := by
                ext <;> unfold Vector3.cross Vector3.scale Vector3.zero <;> ring1
              have scaledBasisSZero :
                  Vector3.scale (form.quadrance axis * form.quadrance axis)
                    basisS = Vector3.zero := by
                calc
                  Vector3.scale (form.quadrance axis * form.quadrance axis)
                      basisS =
                    Vector3.cross
                      (Vector3.scale (form.quadrance axis) basisT)
                      (Vector3.scale (form.quadrance axis) basisR) :=
                    leftCross.symm
                  _ = Vector3.cross
                      (Vector3.scale (form.bilinear basisT axis) axis)
                      (Vector3.scale (form.bilinear basisR axis) axis) := crossed
                  _ = Vector3.zero := rightCross
              have quadranceSquareZero :
                  form.quadrance axis * form.quadrance axis = 0 := by
                have coordinate := congrArg Vector3.s scaledBasisSZero
                simpa [basisS, Vector3.scale] using coordinate
              have quadranceSquareNonzero := ExplicitField.mul_ne_zero
                axisNonNull axisNonNull
              exact (quadranceSquareNonzero quadranceSquareZero).elim
            · exact ⟨sumRS, sumRSPerpendicular, sumRSZero⟩
          · exact ⟨sumTS, sumTSPerpendicular, sumTSZero⟩
        · exact ⟨sumTR, sumTRPerpendicular, sumTRZero⟩
      · exact ⟨projectedS, projectedSPerpendicular, projectedSZero⟩
    · exact ⟨projectedR, projectedRPerpendicular, projectedRZero⟩
  · exact ⟨projectedT, projectedTPerpendicular, projectedTZero⟩

/-! ## Form-relative reflections and half turns -/

/-- Multiply the displayed vector by the retained form matrix to obtain its dual row. -/
def dual (form : Form K) (vector : Vector3 K) : Vector3 K :=
  Matrix3.rowMul vector form.matrix

/-- Pairing against a vector equals the ordinary coordinate dot product against its form dual. -/
theorem bilinear_eq_dot_dual (form : Form K)
    (left right : Vector3 K) :
    form.bilinear left right = Vector3.dot left (form.dual right) := by
  calc
    form.bilinear left right =
        Vector3.dot left
          (Matrix3.rowMul right (Matrix3.transpose form.matrix)) :=
      Matrix3.dot_rowMul_transpose left right form.matrix
    _ = Vector3.dot left (form.dual right) := by
      unfold Form.dual
      rw [form.symmetric]

/-- The form-dual row commutes with scalar multiplication. -/
theorem dual_scale (form : Form K) (scalar : K)
    (vector : Vector3 K) :
    form.dual (Vector3.scale scalar vector) =
      Vector3.scale scalar (form.dual vector) := by
  ext <;> unfold Form.dual Matrix3.rowMul Vector3.scale <;> ring1

/-- Form-relative cross product determined by the displayed volume
coordinates and the cached inverse form matrix.  It is characterized by
`B(u ×_M v, w) = det(u,v,w)`. -/
def cross (form : Form K) (left right : Vector3 K) : Vector3
  K :=
  Matrix3.rowMul (Vector3.cross left right) form.inverse

/-- Applying the form matrix to the relative cross product recovers the
ordinary displayed determinant covector. -/
theorem rowMul_cross_matrix (form : Form K)
    (left right : Vector3 K) :
    Matrix3.rowMul (form.cross left right) form.matrix =
      Vector3.cross left right := by
  unfold Form.cross
  rw [Matrix3.rowMul_mul, form.inverse_mul_matrix,
    Matrix3.rowMul_identity]

/-- Generalized scalar triple-product identity. -/
theorem bilinear_cross (form : Form K)
    (first second third : Vector3 K) :
    form.bilinear (form.cross first second) third =
      Vector3.determinant first second third := by
  unfold Form.bilinear
  rw [form.rowMul_cross_matrix]
  exact Vector3.scalar_triple_product first second third

/-- The form-relative cross product is zero when its left argument is zero. -/
@[simp] theorem cross_zero_left (form : Form K)
    (vector : Vector3 K) : form.cross Vector3.zero vector = Vector3.zero := by
  ext <;> unfold Form.cross Vector3.cross Vector3.zero Matrix3.rowMul <;> ring1

/-- The form-relative cross product is zero when its right argument is zero. -/
@[simp] theorem cross_zero_right (form : Form K)
    (vector : Vector3 K) : form.cross vector Vector3.zero = Vector3.zero := by
  ext <;> unfold Form.cross Vector3.cross Vector3.zero Matrix3.rowMul <;> ring1

/-- Interchanging the two inputs negates the form-relative cross product. -/
theorem cross_anticomm (form : Form K) (left right : Vector3
  K) :
    form.cross left right = Vector3.neg (form.cross right left) := by
  ext <;> unfold Form.cross Vector3.cross Vector3.neg Matrix3.rowMul <;> ring1

/-- The form-relative cross product respects addition in its left argument. -/
theorem cross_add_left (form : Form K)
    (first second third : Vector3 K) :
    form.cross (Vector3.add first second) third =
      Vector3.add (form.cross first third) (form.cross second third) := by
  ext <;> unfold Form.cross Vector3.cross Vector3.add Matrix3.rowMul <;> ring1

/-- The form-relative cross product respects addition in its right argument. -/
theorem cross_add_right (form : Form K)
    (first second third : Vector3 K) :
    form.cross first (Vector3.add second third) =
      Vector3.add (form.cross first second) (form.cross first third) := by
  ext <;> unfold Form.cross Vector3.cross Vector3.add Matrix3.rowMul <;> ring1

/-- The form-relative cross product respects scalar multiplication in its left argument. -/
theorem cross_scale_left (form : Form K) (scalar : K)
    (left right : Vector3 K) :
    form.cross (Vector3.scale scalar left) right =
      Vector3.scale scalar (form.cross left right) := by
  ext <;> unfold Form.cross Vector3.cross Vector3.scale Matrix3.rowMul <;> ring1

/-- The form-relative cross product respects scalar multiplication in its right argument. -/
theorem cross_scale_right (form : Form K) (scalar : K)
    (left right : Vector3 K) :
    form.cross left (Vector3.scale scalar right) =
      Vector3.scale scalar (form.cross left right) := by
  ext <;> unfold Form.cross Vector3.cross Vector3.scale Matrix3.rowMul <;> ring1

/-- The form-relative cross product is perpendicular to its left input in the retained form. -/
theorem cross_perpendicular_left (form : Form K)
    (left right : Vector3 K) :
    form.Perpendicular (form.cross left right) left := by
  unfold Form.Perpendicular
  calc
    form.bilinear (form.cross left right) left =
        Vector3.determinant left right left :=
      form.bilinear_cross left right left
    _ = Vector3.dot (Vector3.cross left right) left :=
      (Vector3.scalar_triple_product left right left).symm
    _ = 0 := Vector3.cross_dot_left left right

/-- The form-relative cross product is perpendicular to its right input in the retained form. -/
theorem cross_perpendicular_right (form : Form K)
    (left right : Vector3 K) :
    form.Perpendicular (form.cross left right) right := by
  unfold Form.Perpendicular
  calc
    form.bilinear (form.cross left right) right =
        Vector3.determinant left right right :=
      form.bilinear_cross left right right
    _ = Vector3.dot (Vector3.cross left right) right :=
      (Vector3.scalar_triple_product left right right).symm
    _ = 0 := Vector3.cross_dot_right left right

/-- The coordinate compound-matrix identity behind the generalized
Binet--Cauchy formula. -/
theorem dot_cross_adjugate_cross (form : Form K)
    (first second third fourth : Vector3 K) :
    Vector3.dot (Vector3.cross first second)
        (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate) =
      form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  rw [form.adjugate_spec]
  unfold Form.bilinear Matrix3.adjugate Matrix3.rowMul Vector3.dot Vector3.cross
  rw [rt_tr, st_ts, sr_rs]
  ring1

/-- Determinant-weighted Binet--Cauchy identity for the form-relative cross
product. -/
theorem binet_cauchy (form : Form K)
    (first second third fourth : Vector3 K) :
    form.determinant *
        form.bilinear (form.cross first second) (form.cross third fourth) =
      form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third := by
  have cancel : form.determinant * form.determinant⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel form.determinant
      form.determinantNonzero
  calc
    form.determinant *
        form.bilinear (form.cross first second) (form.cross third fourth) =
      form.determinant *
        Vector3.dot (Vector3.cross first second) (form.cross third fourth) := by
      unfold Form.bilinear
      rw [form.rowMul_cross_matrix]
    _ = form.determinant *
        Vector3.dot (Vector3.cross first second)
          (Matrix3.rowMul (Vector3.cross third fourth) form.inverse) := rfl
    _ = form.determinant *
        Vector3.dot (Vector3.cross first second)
          (Matrix3.rowMul (Vector3.cross third fourth)
            (Matrix3.scale (1 / form.determinant) form.adjugate)) := by
      rw [form.inverse_eq_scale_adjugate]
    _ = form.determinant *
        ((1 / form.determinant) *
          Vector3.dot (Vector3.cross first second)
            (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate)) := by
      rw [Matrix3.rowMul_scale, Vector3.dot_scale_right]
    _ = Vector3.dot (Vector3.cross first second)
        (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate) := by
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        form.determinant *
            (1 * form.determinant⁻¹ *
              Vector3.dot (Vector3.cross first second)
                (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate)) =
          (form.determinant * form.determinant⁻¹) *
            Vector3.dot (Vector3.cross first second)
              (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate) := by
            ring1
        _ = Vector3.dot (Vector3.cross first second)
            (Matrix3.rowMul (Vector3.cross third fourth) form.adjugate) := by
          rw [cancel, one_mul]
    _ = form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third :=
      form.dot_cross_adjugate_cross first second third fourth

/-- Determinant-weighted Lagrange identity for a general displayed ternary
form. -/
theorem lagrange (form : Form K) (left right : Vector3 K) :
    form.bilinear left right ^ 2 +
        form.determinant * form.quadrance (form.cross left right) =
      form.quadrance left * form.quadrance right := by
  have mixed := form.binet_cauchy left right left right
  unfold Form.quadrance at mixed ⊢
  calc
    form.bilinear left right ^ 2 +
        form.determinant *
          form.bilinear (form.cross left right) (form.cross left right) =
      form.bilinear left right ^ 2 +
        (form.bilinear left left * form.bilinear right right -
          form.bilinear left right * form.bilinear right left) := by
        rw [mixed]
    _ = form.bilinear left left * form.bilinear right right := by
      rw [form.bilinear_comm right left]
      ring1

/-- Determinant-weighted vector triple-product identity. -/
theorem vector_triple_product (form : Form K)
    (first second third : Vector3 K) :
    Vector3.scale form.determinant
        (form.cross first (form.cross second third)) =
      Vector3.sub
        (Vector3.scale (form.bilinear first third) second)
        (Vector3.scale (form.bilinear first second) third) := by
  apply form.eq_of_bilinear_eq
  intro fourth
  have mixed := form.binet_cauchy first fourth second third
  have swapped :
      Vector3.determinant first (form.cross second third) fourth =
        -Vector3.determinant first fourth (form.cross second third) := by
    unfold Vector3.determinant
    ring1
  calc
    form.bilinear
        (Vector3.scale form.determinant
          (form.cross first (form.cross second third))) fourth =
      form.determinant *
        form.bilinear (form.cross first (form.cross second third)) fourth :=
      form.bilinear_scale_left form.determinant _ fourth
    _ = form.determinant *
        Vector3.determinant first (form.cross second third) fourth := by
      rw [form.bilinear_cross]
    _ = -(form.determinant *
        Vector3.determinant first fourth (form.cross second third)) := by
      rw [swapped]
      ring1
    _ = -(form.determinant *
        form.bilinear (form.cross first fourth)
          (form.cross second third)) := by
      rw [form.bilinear_cross]
    _ = -(form.bilinear first second * form.bilinear fourth third -
        form.bilinear first third * form.bilinear fourth second) := by
      rw [mixed]
    _ = form.bilinear
        (Vector3.sub
          (Vector3.scale (form.bilinear first third) second)
          (Vector3.scale (form.bilinear first second) third)) fourth := by
      rw [form.bilinear_sub_left, form.bilinear_scale_left,
        form.bilinear_scale_left, form.bilinear_comm fourth third,
        form.bilinear_comm fourth second]
      ring1

/-- Expand the pairing after subtracting independent multiples of one vector from both arguments.

The result retains both mixed pairings and adds the product of the two scales times the vector quadrance. -/
public theorem bilinear_sub_scale_both (form : Form K)
    (first second vector : Vector3 K) (firstScale secondScale : K) :
    form.bilinear
        (Vector3.sub first (Vector3.scale firstScale vector))
        (Vector3.sub second (Vector3.scale secondScale vector)) =
      form.bilinear first second -
        secondScale * form.bilinear first vector -
        firstScale * form.bilinear vector second +
        firstScale * secondScale * form.quadrance vector := by
  rw [form.bilinear_sub_left, form.bilinear_sub_right,
    form.bilinear_sub_right, form.bilinear_scale_left,
    form.bilinear_scale_left, form.bilinear_scale_right,
    form.bilinear_scale_right]
  unfold Form.quadrance
  ring1

end TernaryForm

end Purelib.Algebra.Quadratic.Ternary.Basic

end
