module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Quadratic.Ternary.Isometry
public import Purelib.Geometry.Quadratic.Ternary.Spread
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

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

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Reflection in the form-perpendicular plane to a non-null vector. The first outer-product argument is the form-dual
vector; for the Euclidean form this reduces to the paper's displayed reflection matrix. -/
def reflection (form : Ternary.Basic.TernaryForm K) (vector :
  Coordinates3.Vector K)
    (_nonNull : form.quadrance vector ≠ 0) : Coordinates3.Matrix3 K :=
  Matrix3.sub Matrix3.identity
    (Matrix3.scale (2 / form.quadrance vector)
      (Matrix3.outer (form.dual vector) vector))

/-- Reflection subtracts twice the bilinear projection onto its non-null normal.

The row-action formula uses the form's quadrance as its explicitly nonzero denominator. -/
theorem rowMul_reflection (form : Ternary.Basic.TernaryForm
  K) (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) (other : Coordinates3.Vector K) :
    Matrix3.rowMul other (form.reflection vector nonNull) =
      Coordinates3.Vector.sub other
        (Coordinates3.Vector.scale
          (2 * form.bilinear other vector / form.quadrance vector) vector) := by
  have bilinearDual := form.bilinear_eq_dot_dual other vector
  ext <;> unfold Ternary.Basic.TernaryForm.reflection Matrix3.rowMul Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Coordinates3.Vector.sub Coordinates3.Vector.scale <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    unfold Ternary.Basic.TernaryForm.bilinear Ternary.Basic.TernaryForm.dual Matrix3.rowMul
      Coordinates3.Vector.dot at bilinearDual ⊢ <;>
    rw [bilinearDual] <;> ring1

/-- If two displayed vectors have the same quadrance and non-null difference, reflection in that difference maps the
first vector to the second. This is the finite reduction step in the constructive Cartan--Dieudonne argument. -/
theorem rowMul_reflection_difference (form :
  Ternary.Basic.TernaryForm K)
    (first second : Coordinates3.Vector K)
    (equalQuadrance : form.quadrance first = form.quadrance second)
    (differenceNonNull :
      form.quadrance (Coordinates3.Vector.sub first second) ≠ 0) :
    Matrix3.rowMul first
        (form.reflection (Coordinates3.Vector.sub first second) differenceNonNull) =
      second := by
  have twiceBilinear :
      2 * form.bilinear first (Coordinates3.Vector.sub first second) =
        form.quadrance (Coordinates3.Vector.sub first second) := by
    calc
      2 * form.bilinear first (Coordinates3.Vector.sub first second) =
          2 * (form.quadrance first - form.bilinear first second) := by
        rw [form.bilinear_sub_right]
        rfl
      _ = form.quadrance first -
          2 * form.bilinear first second + form.quadrance second := by
        rw [← equalQuadrance]
        ring1
      _ = form.quadrance (Coordinates3.Vector.sub first second) :=
        (form.quadrance_sub first second).symm
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (form.quadrance (Coordinates3.Vector.sub first second)) differenceNonNull
  have coefficient :
      2 * form.bilinear first (Coordinates3.Vector.sub first second) /
          form.quadrance (Coordinates3.Vector.sub first second) = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [twiceBilinear, cancel]
  rw [form.rowMul_reflection, coefficient, Coordinates3.Vector.one_scale]
  ext <;> unfold Coordinates3.Vector.sub <;> ring1

/-- The non-null reflection coefficient satisfies the scalar identity giving involutivity. -/
private theorem reflection_coefficient (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0) :
    (2 / form.quadrance vector) ^ 2 * form.quadrance vector =
      2 * (2 / form.quadrance vector) := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (2 * (form.quadrance vector)⁻¹) ^ 2 * form.quadrance vector =
        4 * (form.quadrance vector * (form.quadrance vector)⁻¹) *
          (form.quadrance vector)⁻¹ := by ring1
    _ = 2 * (2 * (form.quadrance vector)⁻¹) := by
      rw [cancel]
      ring1

/-- Reflection in a non-null normal squares to the identity matrix. -/
theorem reflection_square (form : Ternary.Basic.TernaryForm
  K) (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (form.reflection vector nonNull)
      (form.reflection vector nonNull) = Matrix3.identity := by
  have coefficientZero :
      (2 / form.quadrance vector) ^ 2 * form.quadrance vector -
        2 * (2 / form.quadrance vector) = 0 := by
    rw [form.reflection_coefficient vector nonNull]
    ring1
  have dualPair : Coordinates3.Vector.dot vector (form.dual vector) =
      form.quadrance vector := by
    rw [← form.bilinear_eq_dot_dual]
    rfl
  calc
    Matrix3.mul (form.reflection vector nonNull)
        (form.reflection vector nonNull) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          ((2 / form.quadrance vector) ^ 2 *
              Coordinates3.Vector.dot vector (form.dual vector) -
            2 * (2 / form.quadrance vector))
          (Matrix3.outer (form.dual vector) vector)) := by
      ext <;> unfold Ternary.Basic.TernaryForm.reflection Matrix3.mul Matrix3.sub Matrix3.add
        Matrix3.identity Matrix3.scale Matrix3.outer Coordinates3.Vector.dot <;> ring1
    _ =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          ((2 / form.quadrance vector) ^ 2 * form.quadrance vector -
            2 * (2 / form.quadrance vector))
          (Matrix3.outer (form.dual vector) vector)) := by
      rw [dualPair]
    _ = Matrix3.identity := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.outer
        Matrix3.identity <;> ring1

/-- Reflection negates its non-null normal vector. -/
theorem rowMul_self_reflection (form :
  Ternary.Basic.TernaryForm K) (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.rowMul vector (form.reflection vector nonNull) =
      Coordinates3.Vector.neg vector := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  have factor :
      2 * form.bilinear vector vector / form.quadrance vector = (2 : K) := by
    change 2 * form.quadrance vector / form.quadrance vector = (2 : K)
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * form.quadrance vector * (form.quadrance vector)⁻¹ =
          2 * (form.quadrance vector * (form.quadrance vector)⁻¹) := by
        ring1
      _ = 2 := by rw [cancel, mul_one]
  rw [form.rowMul_reflection vector nonNull, factor]
  ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.scale Coordinates3.Vector.neg <;> ring1

/-- Reflection fixes every vector perpendicular to its normal. -/
theorem rowMul_reflection_of_perpendicular (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0)
    (other : Coordinates3.Vector K) (perpendicular : form.Perpendicular other vector) :
    Matrix3.rowMul other (form.reflection vector nonNull) = other := by
  unfold Ternary.Basic.TernaryForm.Perpendicular at perpendicular
  rw [form.rowMul_reflection vector nonNull, perpendicular, mul_zero,
    Algebra.Field.ExplicitField.zero_div]
  ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.scale <;> ring1

/-- Reflection in a non-null normal has determinant minus one. -/
theorem determinant_reflection (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.determinant (form.reflection vector nonNull) = -1 := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  have dualPair : Coordinates3.Vector.dot vector (form.dual vector) =
      form.quadrance vector := by
    rw [← form.bilinear_eq_dot_dual]
    rfl
  unfold Matrix3.determinant Ternary.Basic.TernaryForm.reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    _ = 1 - 2 * (form.quadrance vector)⁻¹ *
        Coordinates3.Vector.dot vector (form.dual vector) := by
      unfold Coordinates3.Vector.dot
      ring1
    _ = 1 - 2 *
        (form.quadrance vector * (form.quadrance vector)⁻¹) := by
      rw [dualPair]
      ring1
    _ = -1 := by rw [cancel]; ring1

/-- The scalar cross terms in bilinear reflection preservation cancel.

The supplied quadrance is nonzero, so both projection denominators may be cancelled. -/
private theorem reflection_bilinear_scalar
    (base first second quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    base - (2 * second / quadrance) * first -
        (2 * first / quadrance) * second +
      (2 * first / quadrance) * (2 * second / quadrance) * quadrance =
      base := by
  have cancel : quadrance * quadrance⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel quadrance quadranceNonzero
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    base - (2 * second * quadrance⁻¹) * first -
          (2 * first * quadrance⁻¹) * second +
        (2 * first * quadrance⁻¹) * (2 * second * quadrance⁻¹) * quadrance =
      base + 4 * first * second * quadrance⁻¹ *
          (quadrance * quadrance⁻¹) -
        4 * first * second * quadrance⁻¹ := by ring1
    _ = base := by rw [cancel]; ring1

/-- The reflection matrix preserves the displayed ternary form. -/
theorem reflection_preservesMatrix (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul
        (Matrix3.mul (form.reflection vector nonNull) form.matrix)
        (Matrix3.transpose (form.reflection vector nonNull)) =
      form.matrix := by
  apply form.preservesMatrix_of_bilinear
  intro first second
  rw [form.rowMul_reflection vector nonNull,
    form.rowMul_reflection vector nonNull,
    form.bilinear_sub_scale_both]
  rw [form.bilinear_comm vector second]
  exact reflection_bilinear_scalar
    (form.bilinear first second)
    (form.bilinear first vector)
    (form.bilinear second vector)
    (form.quadrance vector) nonNull

/-- The reflection packaged as an executable form isometry. -/
def reflectionIsometry (form : Ternary.Basic.TernaryForm K)
  (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) : form.Isometry where
  matrix := form.reflection vector nonNull
  inverseMatrix := form.reflection vector nonNull
  matrix_mul_inverse := form.reflection_square vector nonNull
  inverse_mul_matrix := form.reflection_square vector nonNull
  preservesMatrix := form.reflection_preservesMatrix vector nonNull
end

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- A reflection fixes exactly the directions perpendicular to its non-null normal.

Nonzero two makes the converse implication valid. The retained non-nullity
certificate permits cancelling the normal's quadrance in the row-action formula.
-/
theorem rowMul_reflection_eq_self_iff_perpendicular (form : TernaryForm K)
    (normal : Vector3 K) (nonNull : form.quadrance normal ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K) :
    Matrix3.rowMul vector (form.reflection normal nonNull) = vector ↔
      form.Perpendicular vector normal := by
  constructor
  · intro fixed
    rw [form.rowMul_reflection] at fixed
    have paired := congrArg (form.bilinear normal) fixed
    rw [form.bilinear_sub_right, form.bilinear_scale_right] at paired
    change form.bilinear normal vector -
      (2 * form.bilinear vector normal / form.quadrance normal) * form.quadrance normal =
        form.bilinear normal vector at paired
    have twiceZero : 2 * form.bilinear vector normal = 0 := by
      calc
        2 * form.bilinear vector normal =
            (2 * form.bilinear vector normal / form.quadrance normal) * form.quadrance normal :=
          (ExplicitField.div_mul_cancel _ nonNull).symm
        _ = form.bilinear normal vector -
            (form.bilinear normal vector -
              (2 * form.bilinear vector normal / form.quadrance normal) *
                form.quadrance normal) := by ring1
        _ = 0 := by rw [paired]; ring1
    exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceZero
  · exact form.rowMul_reflection_of_perpendicular normal nonNull vector

/-- A reflection depends only on a non-null normal's line.

Rescaling by a supplied nonzero scalar preserves the reflection matrix. The
scaled non-nullity certificate is constructed from the original normal and scale.
-/
theorem reflection_scale (form : TernaryForm K) (scalar : K) (normal : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (nonNull : form.quadrance normal ≠ 0) :
    form.reflection (Vector3.scale scalar normal)
        (form.quadrance_scale_ne_zero scalar normal scalarNonzero nonNull) =
      form.reflection normal nonNull := by
  have scalarSquareNonzero : scalar ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  have ratio : 2 * scalar ^ 2 / (scalar ^ 2 * form.quadrance normal) =
      2 / form.quadrance normal := by
    apply Ratio.ratio_eq_of_cross_product
    · exact ExplicitField.mul_ne_zero scalarSquareNonzero nonNull
    · exact nonNull
    · ring1
  unfold reflection
  rw [form.quadrance_scale, form.dual_scale]
  calc
    _ = Matrix3.sub Matrix3.identity
        (Matrix3.scale (2 * scalar ^ 2 / (scalar ^ 2 * form.quadrance normal))
          (Matrix3.outer (form.dual normal) normal)) := by
      ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.outer Vector3.scale <;>
        simp only [ExplicitField.div_eq_mul_inv] <;> ring1
    _ = _ := by rw [ratio]

/-- Reversing a non-null normal preserves its reflection matrix. -/
theorem reflection_neg (form : TernaryForm K) (normal : Vector3 K)
    (nonNull : form.quadrance normal ≠ 0) :
    form.reflection (Vector3.neg normal) (by rw [form.quadrance_neg]; exact nonNull) =
      form.reflection normal nonNull := by
  have oneNonzero := Characteristic.Nonzero.one_ne_zero_of_nonzero nonNull
  have negativeOneNonzero : (-1 : K) ≠ 0 := by
    intro equal
    apply oneNonzero
    calc
      (1 : K) = -(-1) := (neg_neg _).symm
      _ = -0 := congrArg Neg.neg equal
      _ = 0 := neg_zero
  have negativeScale : Vector3.scale (-1 : K) normal = Vector3.neg normal := by
    ext <;> unfold Vector3.scale Vector3.neg <;> ring1
  calc
    _ = form.reflection (Vector3.scale (-1) normal)
        (form.quadrance_scale_ne_zero (-1) normal negativeOneNonzero nonNull) := by
      unfold reflection
      rw [negativeScale]
    _ = _ := form.reflection_scale (-1) normal negativeOneNonzero nonNull

/-- Reflection preserves the original form pairing on every pair of row vectors. -/
theorem bilinear_rowMul_reflection (form : TernaryForm K) (normal : Vector3 K)
    (nonNull : form.quadrance normal ≠ 0) (left right : Vector3 K) :
    form.bilinear (Matrix3.rowMul left (form.reflection normal nonNull))
        (Matrix3.rowMul right (form.reflection normal nonNull)) = form.bilinear left right :=
  (form.reflectionIsometry normal nonNull).bilinear_act left right

/-- The trace of two reflections is three minus four times the spread of their normals.

The two retained non-nullity certificates justify cancellation of the
normal quadrances. Symmetry of the original form pairing identifies the
two mixed terms in the rank-one product expansion.
-/
theorem trace_reflection_product (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0) :
    Matrix3.trace (Matrix3.mul (form.reflection first firstNonNull)
        (form.reflection second secondNonNull)) =
      3 - 4 * form.spread first second firstNonNull secondNonNull := by
  have firstCancel := ExplicitField.mul_inv_cancel (form.quadrance first) firstNonNull
  have secondCancel := ExplicitField.mul_inv_cancel (form.quadrance second) secondNonNull
  have productInverse := Purelib.Algebra.Field.Inverse.inverse_product firstNonNull secondNonNull
  calc
    _ = 3 - 2 * (form.quadrance first * (form.quadrance first)⁻¹) -
        2 * (form.quadrance second * (form.quadrance second)⁻¹) +
        4 * form.bilinear first second * form.bilinear second first *
          (form.quadrance first)⁻¹ * (form.quadrance second)⁻¹ := by
      change _ = 3 - 2 * (form.bilinear first first * (form.quadrance first)⁻¹) -
        2 * (form.bilinear second second * (form.quadrance second)⁻¹) +
        4 * form.bilinear first second * form.bilinear second first *
          (form.quadrance first)⁻¹ * (form.quadrance second)⁻¹
      rw [form.bilinear_eq_dot_dual first first, form.bilinear_eq_dot_dual second second,
        form.bilinear_eq_dot_dual first second, form.bilinear_eq_dot_dual second first]
      unfold reflection Matrix3.trace Matrix3.mul Matrix3.sub Matrix3.identity Matrix3.scale Matrix3.outer
        Vector3.dot
      simp only [ExplicitField.div_eq_mul_inv]
      ring1
    _ = 3 - 4 * form.spread first second firstNonNull secondNonNull := by
      rw [firstCancel, secondCancel, form.bilinear_comm second first]
      unfold spread
      simp only [ExplicitField.div_eq_mul_inv, productInverse]
      ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
