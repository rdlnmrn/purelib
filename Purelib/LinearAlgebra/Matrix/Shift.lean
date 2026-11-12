module

public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega

/-!
# Structural nilpotent shifts

The shift moves each original coordinate unit to its successor and discards
the last. Its original finite matrix powers read exact displacement entries,
including beyond the retained dimension, over every commutative coefficient ring.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Shift

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- The original structural shift has unit entries directly below its diagonal. -/
@[expose] def matrix (K : Type*) [CommRing K] (dimension : Nat) : SquareMatrix K dimension :=
  matrixOfFn fun row column => if row.val = column.val + 1 then 1 else 0

/-- The structural shift reads its original one-coordinate displacement test. -/
theorem matrix_apply (row column : Fin dimension) :
    matrix K dimension row column = if row.val = column.val + 1 then 1 else 0 :=
  matrixOfFn_apply _ row column

/-- Left multiplication by the original shift clears the first retained row. -/
theorem mul_first (value : SquareMatrix K (dimension + 1)) (column : Fin (dimension + 1)) :
    Multiplication.mul (matrix K (dimension + 1)) value ⟨0, Nat.zero_lt_succ dimension⟩ column = 0 := by
  rw [Multiplication.mul_apply]
  calc
    _ = sumFin (fun _ : Fin (dimension + 1) => (0 : K)) := by
      apply sumFin_congr
      intro middle
      have different : (0 : Nat) ≠ middle.val + 1 := fun equal => Nat.noConfusion equal
      rw [matrix_apply, if_neg different, zero_mul]
    _ = 0 := sumFin_zero

/-- Left multiplication by the original shift retains the preceding original row. -/
theorem mul_succ (value : SquareMatrix K (dimension + 1)) (row : Fin dimension)
    (column : Fin (dimension + 1)) :
    Multiplication.mul (matrix K (dimension + 1)) value row.succ column = value row.castSucc column := by
  rw [Multiplication.mul_apply]
  calc
    _ = sumFin (fun middle => if middle = row.castSucc then value middle column else 0) := by
      apply sumFin_congr
      intro middle
      rw [matrix_apply]
      by_cases same : middle = row.castSucc
      · have values := congrArg Fin.val same
        have position : row.succ.val = middle.val + 1 := congrArg (· + 1) values.symm
        rw [if_pos position, if_pos same, one_mul]
      · have different : row.succ.val ≠ middle.val + 1 := by
          intro equal
          exact same (Fin.ext (Nat.add_right_cancel equal).symm)
        rw [if_neg different, if_neg same, zero_mul]
    _ = _ := sumFin_ite_eq row.castSucc (fun middle => value middle column)

/-- Every original finite shift power reads exactly its natural coordinate displacement.

No nontriviality or inverse hypothesis is needed. In particular the formula
remains valid when the coefficient ring is the zero ring.
-/
theorem power_apply (exponent : Nat) (row column : Fin dimension) :
    Arithmetic.power (matrix K dimension) exponent row column =
      if row.val = column.val + exponent then 1 else 0 := by
  induction exponent generalizing row column with
  | zero =>
      rw [Arithmetic.power_zero, Multiplication.scaleIdentity_apply, Nat.add_zero]
      by_cases same : row = column
      · rw [if_pos same, if_pos (congrArg Fin.val same)]
      · rw [if_neg same, if_neg (fun equal => same (Fin.ext equal))]
  | succ exponent previous =>
      rw [Arithmetic.power_succ, Multiplication.mul_apply]
      by_cases bounded : column.val + 1 < dimension
      · let next : Fin dimension := ⟨column.val + 1, bounded⟩
        calc
          _ = sumFin (fun middle => if middle = next then
              (if row.val = middle.val + exponent then (1 : K) else 0) else 0) := by
            apply sumFin_congr
            intro middle
            rw [previous row middle, matrix_apply]
            by_cases same : middle = next
            · rw [if_pos same, if_pos (congrArg Fin.val same), mul_one]
            · rw [if_neg same, if_neg (fun equal => same (Fin.ext equal)), mul_zero]
          _ = (if row.val = next.val + exponent then 1 else 0) :=
            sumFin_ite_eq next (fun middle => if row.val = middle.val + exponent then 1 else 0)
          _ = _ := by
            have indices : next.val + exponent = column.val + (exponent + 1) := by
              change column.val + 1 + exponent = column.val + (exponent + 1)
              exact (Nat.add_assoc _ _ _).trans
                (congrArg (fun value => column.val + value) (Nat.add_comm 1 exponent))
            rw [indices]
      · have impossible : row.val ≠ column.val + (exponent + 1) := by
          have rowBound := row.isLt
          omega0
        rw [if_neg impossible]
        calc
          _ = sumFin (fun _ : Fin dimension => (0 : K)) := by
            apply sumFin_congr
            intro middle
            have missing : middle.val ≠ column.val + 1 := by
              have middleBound := middle.isLt
              omega0
            rw [matrix_apply, if_neg missing, mul_zero]
          _ = 0 := sumFin_zero

/-- The dimension-th original shift power is the original structural zero matrix. -/
theorem nilpotent : Arithmetic.power (matrix K dimension) dimension = Arithmetic.zero := by
  apply matrix_ext
  intro row column
  rw [power_apply, Arithmetic.zero_apply]
  have impossible : row.val ≠ column.val + dimension := by
    have rowBound := row.isLt
    omega0
  rw [if_neg impossible]

end Purelib.LinearAlgebra.Matrix.Shift

end
