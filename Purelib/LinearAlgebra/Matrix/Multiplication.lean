module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Vector.Dot
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.TypeStar
import Purelib.Tactic.Ring

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq sumFin_mul_left sumFin_mul_right sumFin_swap)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)

open _root_.Purelib.Data renaming Vector -> Vec

open Purelib.LinearAlgebra renaming Matrix -> Mat

open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply matrix_eq_at matrix_ext)

open Purelib.LinearAlgebra.Vector.Dot (dot)

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Multiplication

universe u
variable {K : Type*} [CommRing K]

/-- Multiply square structural matrices using finite row and column dot products.

Both matrices have the same dimension over a commutative ring. Each result entry is the finite sum of the corresponding
row and column products. -/
def mul {n : Nat} (left right : Mat K n) : Mat K
  n :=
  matrixOfFn fun row column =>
    dot (left row) (vectorOfFn fun middle => right middle column)

/-- Construct a square matrix with one on the diagonal and zero elsewhere. -/
def identity {n : Nat} : Mat K n :=
  matrixOfFn fun row column => if row = column then 1 else 0

/-- Construct a square matrix with the supplied scalar on its diagonal.

Every off-diagonal entry is zero, and the resulting structural matrix retains the given dimension. -/
def scaleIdentity {n : Nat} (a : K) : Mat K n :=
  matrixOfFn fun row column => if row = column then a else 0

open Purelib.LinearAlgebra.Matrix.Multiplication (mul) in
/-- Read a matrix product entry as the finite sum of row and column products.

The bounded intermediate index ranges over the common dimension of the two square matrices. -/
theorem mul_apply {n : Nat} (left right : Mat K
  n)
    (row column : Fin n) :
    mul left right row column =
      sumFin (fun middle => left row middle * right middle column) := by
  unfold mul dot
  rw [matrixOfFn_apply]
  exact sumFin_congr (fun middle => by rw [vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (mul mul_apply) in
/-- Multiplication of square structural matrices is associative.

The three matrices have the same dimension over a commutative ring; the equality is between their retained structural
matrix values. -/
theorem mul_assoc {n : Nat} (first second third :
  Mat K n) :
    mul (mul first second) third = mul first (mul second third) := by
  apply matrix_ext
  intro row column
  calc
    mul (mul first second) third row column =
        sumFin (fun middle =>
          mul first second row middle * third middle column) :=
      mul_apply _ _ row column
    _ = sumFin (fun middle =>
        sumFin (fun inner => first row inner * second inner middle) *
          third middle column) := by
      apply sumFin_congr
      intro middle
      rw [mul_apply]
    _ =
        sumFin (fun middle => sumFin (fun inner =>
          (first row inner * second inner middle) * third middle column)) := by
            apply sumFin_congr
            intro middle
            rw [sumFin_mul_right]
    _ = sumFin (fun inner => sumFin (fun middle =>
          (first row inner * second inner middle) * third middle column)) :=
      sumFin_swap _
    _ = sumFin (fun inner => first row inner *
        sumFin (fun middle => second inner middle * third middle column)) := by
          apply sumFin_congr
          intro inner
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro middle
          ring1
    _ = sumFin (fun inner =>
          first row inner * mul second third inner column) := by
      apply sumFin_congr
      intro inner
      rw [mul_apply]
    _ = mul first (mul second third) row column :=
      (mul_apply _ _ row column).symm

section
open Purelib.LinearAlgebra.Matrix.Multiplication (mul scaleIdentity)
/-- Right multiplication by a scalar identity multiplies every entry on the right.

For a square matrix over a commutative ring, the resulting structural matrix is represented by the displayed
scalar-multiplied entry function. -/
theorem mul_scaleIdentity {n : Nat} (matrix : Mat
  K n) (a : K) :
    mul matrix (scaleIdentity a) =
      fun row column => matrix row column * a := by
  apply matrix_ext
  intro row column
  unfold mul
  rw [matrixOfFn_apply, matrixOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle => matrix row middle *
        (if middle = column then a else 0)) (fun middle => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply])]
  rw [sumFin_congr
      (right := fun middle => if middle = column then
        matrix row middle * a else 0) (fun middle => by
    by_cases equal : middle = column
    · rw [if_pos equal, if_pos equal]
    · rw [if_neg equal, if_neg equal,
        mul_zero])]
  exact sumFin_ite_eq column (fun middle => matrix row middle * a)

/-- Left multiplication by a scalar identity multiplies every entry on the left.

For a square matrix over a commutative ring, the resulting structural matrix is represented by the displayed
scalar-multiplied entry function. -/
theorem scaleIdentity_mul {n : Nat} (a : K)
  (matrix : Mat K n) :
    mul (scaleIdentity a) matrix =
      fun row column => a * matrix row column := by
  apply matrix_ext
  intro row column
  unfold mul
  rw [matrixOfFn_apply, matrixOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle =>
        (if row = middle then a else 0) * matrix middle column)
      (fun middle => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply])]
  rw [sumFin_congr
      (right := fun middle => if middle = row then
        a * matrix middle column else 0) (fun middle => by
    by_cases equal : middle = row
    · subst middle
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg equal, if_neg (Ne.symm equal)]
      rw [_root_.mul_comm, mul_zero])]
  exact sumFin_ite_eq row (fun middle => a * matrix middle column)

end

/-- Multiply a structural column vector by a square matrix.

Each output coordinate is the dot product of the corresponding matrix row with the input vector, at their common finite
dimension. -/
def matrixVector {n : Nat} (matrix : Mat K n)
  (vector : Vec K n) : Vec K n :=
  vectorOfFn fun row => dot (matrix row) vector

/-- Multiply a structural row vector by a square matrix.

Each output coordinate is the dot product of the input vector with the corresponding matrix column, at their common
finite dimension. -/
def vectorMatrix {n : Nat} (vector : Vec K n)
  (matrix : Mat K n) : Vec K n :=
  vectorOfFn fun column =>
    dot vector (vectorOfFn fun row => matrix row column)

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector) in
/-- Read one coordinate of a matrix acting on a column vector.

The coordinate is the finite sum of the selected matrix row multiplied entrywise by the vector. -/
theorem matrixVector_apply {n : Nat} (matrix :
  Mat K n)
    (vector : Vec K n) (row : Fin n) :
    matrixVector matrix vector row =
      sumFin (fun column => matrix row column * vector column) := by
  unfold matrixVector
  rw [vectorOfFn_apply]
  rfl

open Purelib.LinearAlgebra.Matrix.Multiplication (vectorMatrix) in
/-- Read one coordinate of a row vector acting on a matrix.

The coordinate is the finite sum of the vector multiplied entrywise by the selected matrix column. -/
theorem vectorMatrix_apply {n : Nat} (vector :
  Vec K n)
    (matrix : Mat K n) (column : Fin n) :
    vectorMatrix vector matrix column =
      sumFin (fun row => vector row * matrix row column) := by
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  exact sumFin_congr (fun row => by rw [vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (scaleIdentity) in
/-- A scalar identity has its supplied scalar on the diagonal and zero elsewhere. -/
theorem scaleIdentity_apply {n : Nat} (a : K)
  (row column : Fin n) :
    scaleIdentity a row column = if row = column then a else 0 := by
  unfold scaleIdentity
  rw [matrixOfFn_apply]

open Purelib.LinearAlgebra.Matrix.Multiplication (mul mul_apply vectorMatrix) in
/-- Multiplying a displayed matrix row reproduces the corresponding product entry.

The left row is materialized as a structural vector and multiplied by the right matrix at the selected column. -/
theorem vectorMatrix_row_eq_mul_apply {n : Nat}
    (left right : Mat K n) (row column : Fin n) :
    vectorMatrix (vectorOfFn fun i => left row i) right column =
      mul left right row column := by
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  rw [mul_apply]
  exact sumFin_congr (fun i => by
    rw [vectorOfFn_apply, vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (vectorMatrix vectorMatrix_apply) in
/-- Expand a displayed row multiplied by a matrix as a finite entry sum.

At the selected row and column, sum each entry of the left row times the corresponding entry of the right column. -/
theorem vectorMatrix_row_apply {n : Nat}
    (left right : Mat K n) (row column : Fin n) :
    vectorMatrix (vectorOfFn fun i => left row i) right column =
      sumFin (fun i => left row i * right i column) := by
  calc
    vectorMatrix (vectorOfFn fun i => left row i) right column =
        sumFin (fun i => vectorOfFn (fun j => left row j) i *
          right i column) := vectorMatrix_apply _ _ _
    _ = sumFin (fun i => left row i * right i column) :=
      sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- Expand a displayed matrix row dotted with a vector as a finite entry sum.

Materializing the selected row as a structural vector preserves each scalar product in the sum. -/
theorem dot_row_apply {n : Nat} (matrix : Mat K
  n)
    (row : Fin n) (vector : Vec K n) :
    dot (vectorOfFn fun i => matrix row i) vector =
      sumFin (fun i => matrix row i * vector i) := by
  unfold dot
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- Expand a vector dotted with a displayed matrix column as a finite entry sum.

Materializing the selected column as a structural vector preserves each scalar product in the sum. -/
theorem dot_column_apply {n : Nat} (vector : Vec
  K n)
    (matrix : Mat K n) (column : Fin n) :
    dot vector (vectorOfFn fun i => matrix i column) =
      sumFin (fun i => vector i * matrix i column) := by
  unfold dot
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector mul mul_apply) in
/-- Acting on a displayed matrix column reproduces the corresponding product entry.

The right column is materialized as a structural vector, and the left matrix acts on it at the selected row. -/
theorem matrixVector_column_eq_mul_apply {n :
  Nat}
    (left right : Mat K n) (row column : Fin n) :
    matrixVector left (vectorOfFn fun i => right i column) row =
      mul left right row column := by
  unfold matrixVector
  rw [vectorOfFn_apply]
  unfold dot
  rw [mul_apply]
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector matrixVector_apply) in
/-- Expand a matrix acting on a displayed column as a finite entry sum.

At the selected row and column, sum each entry of the left row times the corresponding entry of the right column. -/
theorem matrixVector_column_apply {n : Nat}
    (left right : Mat K n) (row column : Fin n) :
    matrixVector left (vectorOfFn fun i => right i column) row =
      sumFin (fun i => left row i * right i column) := by
  calc
    matrixVector left (vectorOfFn fun i => right i column) row =
        sumFin (fun i => left row i *
          vectorOfFn (fun j => right j column) i) :=
      matrixVector_apply _ _ _
    _ = sumFin (fun i => left row i * right i column) :=
      sumFin_congr (fun i => by rw [vectorOfFn_apply])

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector matrixVector_apply mul mul_apply) in
/-- A matrix product acts on column vectors by successive matrix actions.

The right matrix acts first and the left matrix acts second; all matrices and vectors share one finite dimension over a
commutative ring. -/
theorem matrixVector_mul {n : Nat} (left right :
  Mat K n)
    (vector : Vec K n) :
    matrixVector (mul left right) vector =
      matrixVector left (matrixVector right vector) := by
  apply vector_ext
  intro row
  rw [matrixVector_apply]
  rw [sumFin_congr
    (right := fun middle =>
      sumFin (fun inner => left row inner * right inner middle) *
        vector middle)
    (fun middle => by rw [mul_apply])]
  rw [matrixVector_apply]
  have rightExpansion :
      sumFin (fun inner => left row inner *
          matrixVector right vector inner) =
        sumFin (fun inner => left row inner *
          sumFin (fun middle => right inner middle * vector middle)) :=
    sumFin_congr (fun inner =>
      congrArg (fun entry => left row inner * entry)
        (matrixVector_apply right vector inner))
  rw [rightExpansion]
  calc
    sumFin (fun middle =>
        sumFin (fun inner => left row inner * right inner middle) *
          vector middle) =
        sumFin (fun middle => sumFin (fun inner =>
          (left row inner * right inner middle) * vector middle)) := by
            apply sumFin_congr
            intro middle
            rw [sumFin_mul_right]
    _ = sumFin (fun inner => sumFin (fun middle =>
          (left row inner * right inner middle) * vector middle)) :=
      sumFin_swap _
    _ = sumFin (fun inner => left row inner *
        sumFin (fun middle => right inner middle * vector middle)) := by
          apply sumFin_congr
          intro inner
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro middle
          ring1

open Purelib.LinearAlgebra.Matrix.Multiplication (mul mul_apply vectorMatrix vectorMatrix_apply) in
/-- A row vector acts on a matrix product by successive right actions.

The vector first multiplies the left matrix and then the right matrix, with their common finite dimension retained. -/
theorem vectorMatrix_mul {n : Nat} (vector : Vec
  K n)
    (left right : Mat K n) :
    vectorMatrix vector (mul left right) =
      vectorMatrix (vectorMatrix vector left) right := by
  apply vector_ext
  intro column
  rw [vectorMatrix_apply]
  rw [sumFin_congr
    (right := fun outer => vector outer *
      sumFin (fun inner => left outer inner * right inner column))
    (fun outer => by rw [mul_apply])]
  rw [vectorMatrix_apply]
  have rightExpansion :
      sumFin (fun inner => vectorMatrix vector left inner *
          right inner column) =
        sumFin (fun inner =>
          sumFin (fun outer => vector outer * left outer inner) *
            right inner column) :=
    sumFin_congr (fun inner =>
      congrArg (fun entry => entry * right inner column)
        (vectorMatrix_apply vector left inner))
  rw [rightExpansion]
  calc
    sumFin (fun outer => vector outer *
        sumFin (fun inner => left outer inner * right inner column)) =
      sumFin (fun outer => sumFin (fun inner =>
        vector outer * (left outer inner * right inner column))) := by
          apply sumFin_congr
          intro outer
          rw [← sumFin_mul_left]
    _ = sumFin (fun inner => sumFin (fun outer =>
          vector outer * (left outer inner * right inner column))) :=
      sumFin_swap _
    _ = sumFin (fun inner =>
        sumFin (fun outer => vector outer * left outer inner) *
          right inner column) := by
            apply sumFin_congr
            intro inner
            rw [sumFin_congr
              (right := fun outer => (vector outer * left outer inner) *
                right inner column) (fun _ => by ring1)]
            rw [sumFin_mul_right]

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector vectorMatrix) in
/-- Move a matrix action between the two arguments of a finite dot product.

Dotting a row vector multiplied by the matrix with a second vector equals dotting the original row vector with the
matrix acting on the second vector. -/
theorem dot_vectorMatrix_matrixVector {n : Nat}
  (left : Vec K n)
    (matrix : Mat K n) (right : Vec K n) :
    dot (vectorMatrix left matrix) right =
      dot left (matrixVector matrix right) := by
  unfold dot
  calc
    sumFin (fun column => vectorMatrix left matrix column * right column) =
        sumFin (fun column =>
          sumFin (fun row => left row * matrix row column) * right column) := by
      apply sumFin_congr
      intro column
      unfold vectorMatrix
      rw [vectorOfFn_apply]
      unfold dot
      rw [sumFin_congr (right := fun row =>
        left row * matrix row column) (fun row => by
          rw [vectorOfFn_apply])]
    _ =
        sumFin (fun column => sumFin (fun row =>
          (left row * matrix row column) * right column)) := by
      apply sumFin_congr
      intro column
      rw [sumFin_mul_right]
    _ = sumFin (fun row => sumFin (fun column =>
          (left row * matrix row column) * right column)) :=
      sumFin_swap _
    _ = sumFin (fun row => left row *
        sumFin (fun column => matrix row column * right column)) := by
          apply sumFin_congr
          intro row
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro column
          ring1
    _ = sumFin (fun row => left row * matrixVector matrix right row) := by
      apply sumFin_congr
      intro row
      unfold matrixVector
      rw [vectorOfFn_apply]
      rfl

open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector scaleIdentity) in
/-- A scalar identity acts on a column vector by left scalar multiplication.

The equality retains the structural vector and states that every coordinate is multiplied by the supplied scalar. -/
theorem matrixVector_scaleIdentity {n : Nat} (a :
  K)
    (vector : Vec K n) :
    matrixVector (scaleIdentity a) vector = fun row => a * vector row := by
  apply vector_ext
  intro row
  unfold matrixVector
  rw [vectorOfFn_apply, vectorOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle => if middle = row then
        a * vector middle else 0) (fun middle => by
    unfold scaleIdentity
    rw [matrixOfFn_apply]
    by_cases equal : middle = row
    · subst middle
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg equal, if_neg (Ne.symm equal)]
      rw [_root_.mul_comm,
        mul_zero])]
  exact sumFin_ite_eq row (fun middle => a * vector middle)

open Purelib.LinearAlgebra.Matrix.Multiplication (scaleIdentity vectorMatrix) in
/-- A row vector acts on a scalar identity by right scalar multiplication.

The equality retains the structural vector and states that every coordinate is multiplied by the supplied scalar. -/
theorem vectorMatrix_scaleIdentity {n : Nat}
  (vector : Vec K n)
    (a : K) :
    vectorMatrix vector (scaleIdentity a) = fun column => vector column * a := by
  apply vector_ext
  intro column
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun row => if row = column then vector row * a else 0)
      (fun row => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply]
    by_cases equal : row = column
    · rw [if_pos equal, if_pos equal]
    · rw [if_neg equal, if_neg equal,
        mul_zero])]
  rw [vectorOfFn_apply]
  exact sumFin_ite_eq column (fun row => vector row * a)
end Purelib.LinearAlgebra.Matrix.Multiplication

end

section
@[expose] public section

/-! Exact finite block reads for the square handle-coordinate inverse argument. -/
namespace Purelib.LinearAlgebra.Matrix.Multiplication

variable {K : Type*} [CommRing K]

open Purelib.LinearAlgebra.Matrix.Multiplication (mul mul_scaleIdentity scaleIdentity) in
/-- Right multiplication by the scalar identity at one preserves a square matrix.

The equality holds for structural matrices of any finite dimension over a commutative ring. -/
theorem mul_unit {n : Nat} (matrix : Mat K n) :
  mul matrix (scaleIdentity 1) = matrix := by
  apply matrix_ext
  intro row column
  exact (matrix_eq_at (mul_scaleIdentity matrix 1) row column).trans
    ((matrixOfFn_apply _ row column).trans (mul_one _))

open Purelib.LinearAlgebra.Matrix.Multiplication (mul scaleIdentity scaleIdentity_mul) in
/-- Left multiplication by the scalar identity at one preserves a square matrix.

The equality holds for structural matrices of any finite dimension over a commutative ring. -/
theorem unit_mul {n : Nat} (matrix : Mat K n) :
  mul (scaleIdentity 1) matrix = matrix := by
  apply matrix_ext
  intro row column
  exact (matrix_eq_at (scaleIdentity_mul 1 matrix) row column).trans
    ((matrixOfFn_apply _ row column).trans (one_mul _))

end Purelib.LinearAlgebra.Matrix.Multiplication

end

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.LinearAlgebra.Matrix.Multiplication

/-! ## Folded braid-word action -/

open Purelib.LinearAlgebra.Matrix.Multiplication (identity mul mul_apply)
/-- Right multiplication by the identity preserves an integral matrix.

The equality holds for square structural matrices over the integers, including dimension zero. -/
theorem mul_identity_int {dimension : Nat}
    (matrix : Mat Int dimension) :
    mul matrix identity = matrix := by
  apply matrix_ext
  intro row column
  rw [mul_apply]
  rw [sumFin_congr
    (right := fun middle => if middle = column then matrix row middle else 0)
    (fun middle => by
      unfold identity
      rw [matrixOfFn_apply]
      by_cases equal : middle = column
      · rw [if_pos equal, if_pos equal]
        ring1
      · rw [if_neg equal, if_neg equal]
        ring1)]
  exact sumFin_ite_eq column (fun middle => matrix row middle)

/-- Left multiplication by the identity preserves an integral matrix.

The equality holds for square structural matrices over the integers, including dimension zero. -/
theorem identity_mul_int {dimension : Nat}
    (matrix : Mat Int dimension) :
    mul identity matrix = matrix := by
  apply matrix_ext
  intro row column
  rw [mul_apply]
  rw [sumFin_congr
    (right := fun middle => if middle = row then matrix middle column else 0)
    (fun middle => by
      unfold identity
      rw [matrixOfFn_apply]
      by_cases equal : middle = row
      · subst middle
        rw [if_pos rfl, if_pos rfl]
        ring1
      · rw [if_neg equal, if_neg (Ne.symm equal)]
        ring1)]
  exact sumFin_ite_eq row (fun middle => matrix middle column)
end Purelib.LinearAlgebra.Matrix.Multiplication

end
