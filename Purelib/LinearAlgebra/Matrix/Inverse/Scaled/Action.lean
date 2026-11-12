module

public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Vector.Dot
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Action

open Purelib
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.Vector.Basic
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K]

public section

set_option genInjectivity false in
/-- The original scaled inverse applied to one retained right-hand side.

Both readbacks identify the canonical fraction-free computation, even when its
scalar vanishes. Producing the action need not materialize the inverse matrix. -/
structure Applied {n : Nat} (matrix : SquareMatrix K n) (right : Data.Vector K n) where
  /-- The exact scalar of the canonical scaled inverse. -/
  scalar : K
  /-- The scalar agrees with the original matrix computation. -/
  scalar_eq : scalar = (Compute.scaledInverse matrix).scalar
  /-- The original inverse matrix applied to the retained vector. -/
  values : Data.Vector K n
  /-- The action agrees with multiplication by the original computed inverse. -/
  values_eq : values = Multiplication.matrixVector
    (Compute.scaledInverse matrix).inverse right

constructive_injectivity Applied

end

/-- A matrix action distributes over a displayed scaled difference of vectors. -/
private theorem matrixVector_difference {n : Nat} (matrix : SquareMatrix K n)
    (left right : Data.Vector K n) (a b : K) (row : Fin n) :
    Multiplication.matrixVector matrix
      (vectorOfFn fun index => a * left index - b * right index) row =
      a * Multiplication.matrixVector matrix left row -
        b * Multiplication.matrixVector matrix right row := by
  rewrite [Multiplication.matrixVector_apply]
  rewrite [sumFin_congr (right := fun index =>
    a * (matrix row index * left index) - b * (matrix row index * right index))
    (fun index => by rewrite [vectorOfFn_apply]; ring1)]
  rewrite [sumFin_sub, sumFin_mul_left, sumFin_mul_left]
  rewrite [Multiplication.matrixVector_apply,
    Multiplication.matrixVector_apply]
  rfl

/-- The block inverse action uses the smaller inverse on one corrected vector. -/
private theorem block_action {n : Nat} (matrix : SquareMatrix K (n + 1))
    (right : Data.Vector K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) :
    let first : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let tail := vectorOfFn fun index : Fin n => right index.succ
    let corrected := vectorOfFn fun index =>
      Blocks.head matrix * tail index -
        right first * Blocks.leftColumn matrix index
    let action := Multiplication.matrixVector smaller.inverse corrected
    Data.Vector.cons
      (smaller.scalar * right first - Dot.dot (Blocks.topRow matrix) action)
      (vectorOfFn fun index => Blocks.head matrix * action index) =
      Multiplication.matrixVector (Block.blockInverse matrix smaller) right := by
  dsimp only
  let first : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let tail := vectorOfFn fun index : Fin n => right index.succ
  let a := Blocks.head matrix
  let row := Blocks.topRow matrix
  let column := Blocks.leftColumn matrix
  let corrected := vectorOfFn fun index => a * tail index - right first * column index
  let action := Multiplication.matrixVector smaller.inverse corrected
  have actionAt (index : Fin n) : action index =
      a * Multiplication.matrixVector smaller.inverse tail index -
        right first * Multiplication.matrixVector smaller.inverse column index :=
    matrixVector_difference smaller.inverse tail column a (right first) index
  have dotAction : Dot.dot row action =
      a * Dot.dot row (Multiplication.matrixVector smaller.inverse tail) -
        right first * Dot.dot row (Multiplication.matrixVector smaller.inverse column) := by
    unfold Dot.dot
    rewrite [sumFin_congr (right := fun index =>
      a * (row index * Multiplication.matrixVector smaller.inverse tail index) -
        right first * (row index * Multiplication.matrixVector smaller.inverse column index))
      (fun index => by rewrite [actionAt]; ring1)]
    rewrite [sumFin_sub, sumFin_mul_left, sumFin_mul_left]
    rfl
  apply vector_ext
  intro index
  refine Data.Fin.cases_induction ?_ (fun tailIndex => ?_) index
  · change smaller.scalar * right first - Dot.dot row action = _
    rewrite [Multiplication.matrixVector_apply (Block.blockInverse matrix smaller) right first,
      sumFin_succ]
    rewrite [Block.blockInverse_apply]
    rewrite [sumFin_congr (right := fun index =>
      -a * (Multiplication.vectorMatrix row smaller.inverse index * tail index))
      (fun index => by
        rewrite [Block.blockInverse_apply]
        dsimp only [first]
        simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
        dsimp only [tail, a, row]
        rewrite [vectorOfFn_apply]
        ring1)]
    rewrite [sumFin_mul_left]
    change smaller.scalar * right first - Dot.dot row action =
      (smaller.scalar + Dot.dot row (Multiplication.matrixVector smaller.inverse column)) *
        right first + -a * Dot.dot (Multiplication.vectorMatrix row smaller.inverse) tail
    rewrite [Multiplication.dot_vectorMatrix_matrixVector, dotAction]
    ring1
  · change (vectorOfFn fun index => a * action index) tailIndex = _
    rewrite [vectorOfFn_apply, actionAt]
    rewrite [Multiplication.matrixVector_apply (Block.blockInverse matrix smaller) right tailIndex.succ,
      sumFin_succ]
    rewrite [Block.blockInverse_apply]
    simp only [Data.Fin.cases_succ]
    rewrite [sumFin_congr (right := fun index =>
      a ^ 2 * (smaller.inverse tailIndex index * tail index))
      (fun index => by
        rewrite [Block.blockInverse_apply]
        simp only [Data.Fin.cases_succ]
        dsimp only [tail, a]
        rewrite [vectorOfFn_apply]
        ring1)]
    rewrite [sumFin_mul_left]
    rewrite [Multiplication.matrixVector_apply]
    change a * (a * sumFin (fun index => smaller.inverse tailIndex index * tail index) -
        right first * Multiplication.matrixVector smaller.inverse column tailIndex) =
      (-a * Multiplication.matrixVector smaller.inverse column tailIndex) * right first +
        a ^ 2 * sumFin (fun index => smaller.inverse tailIndex index * tail index)
    ring1

public section

/-- Compute one canonical scaled-inverse action without constructing the inverse.

The recursion retains the same Schur matrices and scalars as `scaledInverse`.
At each stage it computes only the corrected right-hand side and the resulting
smaller action. No invertibility or nonzero pivot assumption is required. -/
@[expose] def compute : {n : Nat} → (matrix : SquareMatrix K n) →
    (right : Data.Vector K n) → Applied matrix right
  | 0, matrix, right =>
      { scalar := 1
        scalar_eq := rfl
        values := .nil
        values_eq := vector_ext (fun index => Fin.elim0 index) }
  | n + 1, matrix, right =>
      let first : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      let a := Blocks.head matrix
      let tail := vectorOfFn fun index : Fin n => right index.succ
      let corrected := vectorOfFn fun index =>
        a * tail index - right first * Blocks.leftColumn matrix index
      let smaller := compute (Schur.schur matrix) corrected
      { scalar := a * smaller.scalar
        scalar_eq := by
          rewrite [smaller.scalar_eq]
          rfl
        values := Data.Vector.cons
          (smaller.scalar * right first - Dot.dot (Blocks.topRow matrix) smaller.values)
          (vectorOfFn fun index => a * smaller.values index)
        values_eq := by
          rewrite [smaller.scalar_eq, smaller.values_eq]
          exact block_action matrix right (Compute.scaledInverse (Schur.schur matrix)) }

end

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Action
