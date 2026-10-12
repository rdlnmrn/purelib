module
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

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

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section TernaryForm

/-- Applying a displayed matrix to all three rows scales their displayed determinant by the matrix determinant. -/
theorem determinant_rowMul (first second third :
  Coordinates3.Vector K)
    (matrix : Coordinates3.Matrix3 K) :
    Coordinates3.Vector.determinant
        (Matrix3.rowMul first matrix)
        (Matrix3.rowMul second matrix)
        (Matrix3.rowMul third matrix) =
      Coordinates3.Vector.determinant first second third *
        Matrix3.determinant matrix := by
  unfold Coordinates3.Vector.determinant Matrix3.rowMul Matrix3.determinant
  ring1

/-- Explicit reconstruction in a displayed pairwise-orthogonal non-null frame. The proof builds the displayed frame
matrix and its right inverse, then uses finite square-matrix cancellation to obtain the left inverse. -/
theorem orthogonalFrame_reconstruct
    (form : Ternary.Basic.TernaryForm K) (first second third : Coordinates3.Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (thirdNonNull : form.quadrance third ≠ 0)
    (firstSecond : form.Perpendicular first second)
    (firstThird : form.Perpendicular first third)
    (secondThird : form.Perpendicular second third)
    (vector : Coordinates3.Vector K) :
    Coordinates3.Vector.add
        (Coordinates3.Vector.add
          (Coordinates3.Vector.scale
            (form.bilinear vector first / form.quadrance first) first)
          (Coordinates3.Vector.scale
            (form.bilinear vector second / form.quadrance second) second))
        (Coordinates3.Vector.scale
          (form.bilinear vector third / form.quadrance third) third) =
      vector := by
  let basisMatrix : Coordinates3.Matrix3 K :=
    ⟨first.t, first.r, first.s,
      second.t, second.r, second.s,
      third.t, third.r, third.s⟩
  let inverseMatrix : Coordinates3.Matrix3 K :=
    ⟨(form.dual first).t / form.quadrance first,
      (form.dual second).t / form.quadrance second,
      (form.dual third).t / form.quadrance third,
      (form.dual first).r / form.quadrance first,
      (form.dual second).r / form.quadrance second,
      (form.dual third).r / form.quadrance third,
      (form.dual first).s / form.quadrance first,
      (form.dual second).s / form.quadrance second,
      (form.dual third).s / form.quadrance third⟩
  have rowMulInverse (input : Coordinates3.Vector K) :
      Matrix3.rowMul input inverseMatrix =
        (⟨form.bilinear input first / form.quadrance first,
          form.bilinear input second / form.quadrance second,
          form.bilinear input third / form.quadrance third⟩ :
          Coordinates3.Vector K) := by
    apply Coordinates3.Vector.ext
    · change
        input.t * ((form.dual first).t / form.quadrance first) +
              input.r * ((form.dual first).r / form.quadrance first) +
              input.s * ((form.dual first).s / form.quadrance first) =
          form.bilinear input first / form.quadrance first
      rw [form.bilinear_eq_dot_dual]
      unfold Coordinates3.Vector.dot
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
    · change
        input.t * ((form.dual second).t / form.quadrance second) +
              input.r * ((form.dual second).r / form.quadrance second) +
              input.s * ((form.dual second).s / form.quadrance second) =
          form.bilinear input second / form.quadrance second
      rw [form.bilinear_eq_dot_dual]
      unfold Coordinates3.Vector.dot
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
    · change
        input.t * ((form.dual third).t / form.quadrance third) +
              input.r * ((form.dual third).r / form.quadrance third) +
              input.s * ((form.dual third).s / form.quadrance third) =
          form.bilinear input third / form.quadrance third
      rw [form.bilinear_eq_dot_dual]
      unfold Coordinates3.Vector.dot
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
  have rowMulBasis (coordinates : Coordinates3.Vector K) :
      Matrix3.rowMul coordinates basisMatrix =
        Coordinates3.Vector.add
          (Coordinates3.Vector.add
            (Coordinates3.Vector.scale coordinates.t first)
            (Coordinates3.Vector.scale coordinates.r second))
          (Coordinates3.Vector.scale coordinates.s third) := by
    ext <;> unfold basisMatrix Matrix3.rowMul Coordinates3.Vector.add Coordinates3.Vector.scale <;>
      ring1
  have firstSecondZero : form.bilinear first second = 0 := firstSecond
  have firstThirdZero : form.bilinear first third = 0 := firstThird
  have secondThirdZero : form.bilinear second third = 0 := secondThird
  have secondFirstZero : form.bilinear second first = 0 := by
    rw [form.bilinear_comm]
    exact firstSecondZero
  have thirdFirstZero : form.bilinear third first = 0 := by
    rw [form.bilinear_comm]
    exact firstThirdZero
  have thirdSecondZero : form.bilinear third second = 0 := by
    rw [form.bilinear_comm]
    exact secondThirdZero
  have firstRatio : form.quadrance first / form.quadrance first = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    exact Algebra.Field.ExplicitField.mul_inv_cancel
      (form.quadrance first) firstNonNull
  have secondRatio : form.quadrance second / form.quadrance second = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    exact Algebra.Field.ExplicitField.mul_inv_cancel
      (form.quadrance second) secondNonNull
  have thirdRatio : form.quadrance third / form.quadrance third = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    exact Algebra.Field.ExplicitField.mul_inv_cancel
      (form.quadrance third) thirdNonNull
  have firstRow :
      Matrix3.rowMul first inverseMatrix = (⟨1, 0, 0⟩ : Coordinates3.Vector K) := by
    rw [rowMulInverse]
    apply Coordinates3.Vector.ext
    · change form.quadrance first / form.quadrance first = 1
      exact firstRatio
    · change form.bilinear first second / form.quadrance second = 0
      rw [firstSecondZero, Algebra.Field.ExplicitField.zero_div]
    · change form.bilinear first third / form.quadrance third = 0
      rw [firstThirdZero, Algebra.Field.ExplicitField.zero_div]
  have secondRow :
      Matrix3.rowMul second inverseMatrix = (⟨0, 1, 0⟩ : Coordinates3.Vector K) := by
    rw [rowMulInverse]
    apply Coordinates3.Vector.ext
    · change form.bilinear second first / form.quadrance first = 0
      rw [secondFirstZero, Algebra.Field.ExplicitField.zero_div]
    · change form.quadrance second / form.quadrance second = 1
      exact secondRatio
    · change form.bilinear second third / form.quadrance third = 0
      rw [secondThirdZero, Algebra.Field.ExplicitField.zero_div]
  have thirdRow :
      Matrix3.rowMul third inverseMatrix = (⟨0, 0, 1⟩ : Coordinates3.Vector K) := by
    rw [rowMulInverse]
    apply Coordinates3.Vector.ext
    · change form.bilinear third first / form.quadrance first = 0
      rw [thirdFirstZero, Algebra.Field.ExplicitField.zero_div]
    · change form.bilinear third second / form.quadrance second = 0
      rw [thirdSecondZero, Algebra.Field.ExplicitField.zero_div]
    · change form.quadrance third / form.quadrance third = 1
      exact thirdRatio
  have rightInverse :
      Matrix3.mul basisMatrix inverseMatrix = Matrix3.identity := by
    apply Matrix3.ext
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.t firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.r firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.s firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.t secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.r secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.s secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.t thirdRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.r thirdRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Coordinates3.Vector.s thirdRow
  have leftInverse :
      Matrix3.mul inverseMatrix basisMatrix = Matrix3.identity :=
    Matrix3.inverse_mul_of_mul_eq_identity form.one_ne_zero rightInverse
  calc
    Coordinates3.Vector.add
        (Coordinates3.Vector.add
          (Coordinates3.Vector.scale
            (form.bilinear vector first / form.quadrance first) first)
          (Coordinates3.Vector.scale
            (form.bilinear vector second / form.quadrance second) second))
        (Coordinates3.Vector.scale
          (form.bilinear vector third / form.quadrance third) third) =
      Matrix3.rowMul
        (⟨form.bilinear vector first / form.quadrance first,
          form.bilinear vector second / form.quadrance second,
          form.bilinear vector third / form.quadrance third⟩ : Coordinates3.Vector K)
        basisMatrix :=
      (rowMulBasis
        (⟨form.bilinear vector first / form.quadrance first,
          form.bilinear vector second / form.quadrance second,
          form.bilinear vector third / form.quadrance third⟩ :
          Coordinates3.Vector K)).symm
    _ = Matrix3.rowMul
        (Matrix3.rowMul vector inverseMatrix) basisMatrix := by
      rw [rowMulInverse]
    _ = Matrix3.rowMul vector
        (Matrix3.mul inverseMatrix basisMatrix) :=
      Matrix3.rowMul_mul vector inverseMatrix basisMatrix
    _ = Matrix3.rowMul vector Matrix3.identity := by rw [leftInverse]
    _ = vector := Matrix3.rowMul_identity vector

/-- The relative cross of two perpendicular non-null vectors is non-null. -/
theorem cross_nonNull_of_perpendicular
    (form : Ternary.Basic.TernaryForm K) (first second : Coordinates3.Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (perpendicular : form.Perpendicular first second) :
    form.quadrance (form.cross first second) ≠ 0 := by
  intro crossZero
  have perpendicularZero : form.bilinear first second = 0 := perpendicular
  have lagrange := form.lagrange first second
  rw [perpendicularZero, crossZero] at lagrange
  have productNonzero :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  apply productNonzero
  calc
    form.quadrance first * form.quadrance second =
        0 ^ 2 + form.determinant * 0 := lagrange.symm
    _ = 0 := by ring1

namespace Isometry

/-- A determinant-one form isometry fixing two perpendicular non-null vectors is the identity. The relative cross
supplies the third non-null frame vector, and the determinant fixes its otherwise possible scalar action. -/
theorem
  matrix_eq_identity_of_fixed_orthogonal_pair
    (form : Ternary.Basic.TernaryForm K) (isometry : form.Isometry)
    (first second : Coordinates3.Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (perpendicular : form.Perpendicular first second)
    (firstFixed : (Isometry.act isometry) first = first)
    (secondFixed : (Isometry.act isometry) second = second)
    (determinantOne : Matrix3.determinant isometry.matrix = 1) :
    isometry.matrix = Matrix3.identity := by
  let third := form.cross first second
  have thirdNonNull : form.quadrance third ≠ 0 :=
    form.cross_nonNull_of_perpendicular first second firstNonNull
      secondNonNull perpendicular
  have firstThird : form.Perpendicular first third := by
    apply (form.perpendicular_comm first third).2
    exact form.cross_perpendicular_left first second
  have secondThird : form.Perpendicular second third := by
    apply (form.perpendicular_comm second third).2
    exact form.cross_perpendicular_right first second
  have thirdActFirstZero :
      form.bilinear ((Isometry.act isometry) third) first = 0 := by
    calc
      form.bilinear ((Isometry.act isometry) third) first =
          form.bilinear ((Isometry.act isometry) third) ((Isometry.act isometry) first) := by
        rw [firstFixed]
      _ = form.bilinear third first :=
        (Isometry.bilinear_act isometry) third first
      _ = 0 := form.cross_perpendicular_left first second
  have thirdActSecondZero :
      form.bilinear ((Isometry.act isometry) third) second = 0 := by
    calc
      form.bilinear ((Isometry.act isometry) third) second =
          form.bilinear ((Isometry.act isometry) third) ((Isometry.act isometry) second) := by
        rw [secondFixed]
      _ = form.bilinear third second :=
        (Isometry.bilinear_act isometry) third second
      _ = 0 := form.cross_perpendicular_right first second
  let thirdCoefficient :=
    form.bilinear ((Isometry.act isometry) third) third / form.quadrance third
  have thirdActScale :
      (Isometry.act isometry) third = Coordinates3.Vector.scale thirdCoefficient third := by
    have reconstruction := form.orthogonalFrame_reconstruct
      first second third firstNonNull secondNonNull thirdNonNull
      perpendicular firstThird secondThird ((Isometry.act isometry) third)
    calc
      (Isometry.act isometry) third =
          Coordinates3.Vector.add
            (Coordinates3.Vector.add
              (Coordinates3.Vector.scale
                (form.bilinear ((Isometry.act isometry) third) first /
                  form.quadrance first) first)
              (Coordinates3.Vector.scale
                (form.bilinear ((Isometry.act isometry) third) second /
                  form.quadrance second) second))
            (Coordinates3.Vector.scale
              (form.bilinear ((Isometry.act isometry) third) third /
                form.quadrance third) third) :=
        reconstruction.symm
      _ = Coordinates3.Vector.scale thirdCoefficient third := by
        rw [thirdActFirstZero, thirdActSecondZero,
          Algebra.Field.ExplicitField.zero_div, Algebra.Field.ExplicitField.zero_div]
        ext <;> unfold thirdCoefficient Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1
  have frameDeterminant :
      Coordinates3.Vector.determinant first second third = form.quadrance third := by
    exact (form.bilinear_cross first second third).symm
  have transformedDeterminant :=
    determinant_rowMul first second third isometry.matrix
  change Coordinates3.Vector.determinant
      ((Isometry.act isometry) first) ((Isometry.act isometry) second) ((Isometry.act isometry) third) =
    Coordinates3.Vector.determinant first second third *
      Matrix3.determinant isometry.matrix at transformedDeterminant
  rw [firstFixed, secondFixed, thirdActScale, determinantOne,
    mul_one] at transformedDeterminant
  have coefficientFrame :
      thirdCoefficient * Coordinates3.Vector.determinant first second third =
        Coordinates3.Vector.determinant first second third := by
    calc
      thirdCoefficient * Coordinates3.Vector.determinant first second third =
          Coordinates3.Vector.determinant first second
            (Coordinates3.Vector.scale thirdCoefficient third) := by
        unfold Coordinates3.Vector.determinant Coordinates3.Vector.scale
        ring1
      _ = Coordinates3.Vector.determinant first second third :=
        transformedDeterminant
  have coefficientOne : thirdCoefficient = 1 := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left thirdNonNull
    calc
      form.quadrance third * thirdCoefficient =
          thirdCoefficient * Coordinates3.Vector.determinant first second third := by
        rw [frameDeterminant]
        ring1
      _ = Coordinates3.Vector.determinant first second third := coefficientFrame
      _ = form.quadrance third * 1 := by
        rw [frameDeterminant, mul_one]
  have thirdFixed : (Isometry.act isometry) third = third := by
    rw [thirdActScale, coefficientOne, Coordinates3.Vector.one_scale]
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  change (Isometry.act isometry) vector =
    Matrix3.rowMul vector Matrix3.identity
  rw [Matrix3.rowMul_identity]
  have reconstruction := form.orthogonalFrame_reconstruct
    first second third firstNonNull secondNonNull thirdNonNull
    perpendicular firstThird secondThird vector
  calc
    (Isometry.act isometry) vector =
        (Isometry.act isometry)
          (Coordinates3.Vector.add
            (Coordinates3.Vector.add
              (Coordinates3.Vector.scale
                (form.bilinear vector first / form.quadrance first) first)
              (Coordinates3.Vector.scale
                (form.bilinear vector second / form.quadrance second) second))
            (Coordinates3.Vector.scale
              (form.bilinear vector third / form.quadrance third) third)) := by
      rw [reconstruction]
    _ = Coordinates3.Vector.add
          (Coordinates3.Vector.add
            (Coordinates3.Vector.scale
              (form.bilinear vector first / form.quadrance first)
              ((Isometry.act isometry) first))
            (Coordinates3.Vector.scale
              (form.bilinear vector second / form.quadrance second)
              ((Isometry.act isometry) second)))
          (Coordinates3.Vector.scale
            (form.bilinear vector third / form.quadrance third)
            ((Isometry.act isometry) third)) := by
      ext <;> unfold Isometry.act Matrix3.rowMul Coordinates3.Vector.add Coordinates3.Vector.scale <;>
        ring1
    _ = Coordinates3.Vector.add
          (Coordinates3.Vector.add
            (Coordinates3.Vector.scale
              (form.bilinear vector first / form.quadrance first) first)
            (Coordinates3.Vector.scale
              (form.bilinear vector second / form.quadrance second) second))
          (Coordinates3.Vector.scale
            (form.bilinear vector third / form.quadrance third) third) := by
      rw [firstFixed, secondFixed, thirdFixed]
    _ = vector := reconstruction

end Isometry

end TernaryForm

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] {form : Ternary.Basic.TernaryForm K}

/-- A perpendicular vector cannot be a nonzero multiple of an original non-null vector. -/
theorem nonNull_perpendicular_not_same_line (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (perpendicular : form.Perpendicular second first) :
    ¬ ∃ factor : K, factor ≠ 0 ∧ second = Vector3.scale factor first := by
  rintro ⟨factor, factorNonzero, scaled⟩
  have productZero : factor * form.quadrance first = 0 := by
    change form.bilinear second first = 0 at perpendicular
    rw [scaled, form.bilinear_scale_left] at perpendicular
    exact perpendicular
  exact ExplicitField.mul_ne_zero factorNonzero firstNonNull productZero

namespace PerpendicularNonNullVectorWitness

/-- Construct a different non-null perpendicular line from a retained first line.

For a non-null axis, the original relative cross gives a perpendicular
second direction. For a nonzero null axis, adding that axis preserves the
first quadrance and changes its line. At the zero axis, the finite
perpendicular-vector construction is applied to the original first vector.
Each branch retains the original axis and proves explicit line distinction.
-/
@[expose] def alternateDirection [DecidableEq K] {axis : Vector3 K}
    (first : form.PerpendicularNonNullVectorWitness axis) (twoNonzero : (2 : K) ≠ 0) :
    Σ' second : form.PerpendicularNonNullVectorWitness axis,
      ¬ ∃ factor : K, factor ≠ 0 ∧ second.value = Vector3.scale factor first.value := by
  by_cases axisNull : form.quadrance axis = 0
  · by_cases axisZero : axis = Vector3.zero
    · let second := form.perpendicularNonNullVectorWitness first.value first.nonNull twoNonzero
      refine ⟨⟨second.value, ?_, second.nonNull⟩, ?_⟩
      · change form.bilinear second.value axis = 0
        exact (congrArg (fun vector : Vector3 K => form.bilinear second.value vector) axisZero).trans
          (form.bilinear_zero_right second.value)
      · exact nonNull_perpendicular_not_same_line first.value second.value first.nonNull second.perpendicular
    · have pairing : form.bilinear axis first.value = 0 := by
        rw [form.bilinear_comm]
        exact first.perpendicular
      have quadranceEqual : form.quadrance (Vector3.add first.value axis) = form.quadrance first.value := by
        rw [form.quadrance_add, first.perpendicular, axisNull]
        ring1
      have nonNull : form.quadrance (Vector3.add first.value axis) ≠ 0 :=
        fun zero => first.nonNull (quadranceEqual.symm.trans zero)
      refine ⟨⟨Vector3.add first.value axis, ?_, nonNull⟩, ?_⟩
      · change form.bilinear (Vector3.add first.value axis) axis = 0
        rw [form.bilinear_add_left, first.perpendicular]
        change 0 + form.quadrance axis = 0
        rw [axisNull, add_zero]
      · rintro ⟨factor, _factorNonzero, scaled⟩
        change Vector3.add first.value axis = Vector3.scale factor first.value at scaled
        have pairEqual := congrArg (fun value : Vector3 K => form.bilinear value first.value) scaled
        rw [form.bilinear_add_left, pairing, form.bilinear_scale_left, add_zero] at pairEqual
        have factorOne : factor = 1 := by
          apply ExplicitField.eq_of_mul_eq_mul_right first.nonNull
          rw [one_mul]
          exact pairEqual.symm
        rw [factorOne, Vector3.one_scale] at scaled
        have axisRecovered : axis = Vector3.sub (Vector3.add first.value axis) first.value := by
          ext <;> unfold Vector3.sub Vector3.add <;> ring1
        rw [scaled] at axisRecovered
        have zeroDifference : Vector3.sub first.value first.value = Vector3.zero := by
          ext <;> unfold Vector3.sub Vector3.zero <;> ring1
        exact axisZero (axisRecovered.trans zeroDifference)
  · have axisFirst : form.Perpendicular axis first.value :=
      (form.perpendicular_comm axis first.value).mpr first.perpendicular
    let second : form.PerpendicularNonNullVectorWitness axis :=
      ⟨form.cross axis first.value, form.cross_perpendicular_left axis first.value,
        form.cross_nonNull_of_perpendicular axis first.value axisNull first.nonNull axisFirst⟩
    exact ⟨second, nonNull_perpendicular_not_same_line first.value second.value first.nonNull
      (form.cross_perpendicular_right axis first.value)⟩

end PerpendicularNonNullVectorWitness

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
