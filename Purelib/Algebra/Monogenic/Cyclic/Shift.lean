module

public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.LinearAlgebra.Matrix.Shift
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Cyclic tables of structural nilpotent shifts

One original cached power table sends the first retained coordinate to each
coordinate unit in turn. This construction fixes its positive dimension
without testing a polynomial degree, including over the zero coefficient ring.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic

open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K]

/-- Build the original nilpotent shift's cyclic certificate with one cached successive power traversal. -/
@[expose] def shift (K : Type*) [CommRing K] (dimension : Nat) (positive : 0 < dimension) :
    Cyclic (Shift.matrix K dimension) where
  origin := ⟨0, positive⟩
  powers := Arithmetic.powerTable (Shift.matrix K dimension) dimension
  powers_eq := Arithmetic.powerTable_apply _ _
  coordinate := by
    intro index row
    rw [Arithmetic.powerTable_apply, Shift.power_apply]
    change (if row.val = 0 + index.val then (1 : K) else 0) = if row = index then 1 else 0
    rw [Nat.zero_add]
    by_cases same : row = index
    · rw [if_pos (congrArg Fin.val same), if_pos same]
    · rw [if_neg (fun equal => same (Fin.ext equal)), if_neg same]

namespace Element

/-- Every original nilpotent cyclic element has zero first-row entries after its first column. -/
theorem shift_first_row {dimension : Nat} {cyclic : Cyclic (Shift.matrix K (dimension + 1))}
    (value : Element cyclic) (column : Fin dimension) :
    value.matrix ⟨0, Nat.zero_lt_succ dimension⟩ column.succ = 0 := by
  calc
    _ = sumFin (fun index => value.matrix index cyclic.origin *
        cyclic.powers index ⟨0, Nat.zero_lt_succ dimension⟩ column.succ) :=
      cyclic.reconstruct_entry value.matrix value.commutes _ _
    _ = sumFin (fun _ : Fin (dimension + 1) => (0 : K)) := by
      apply sumFin_congr
      intro index
      rw [cyclic.powers_eq, Shift.power_apply]
      have impossible : (0 : Nat) ≠ column.succ.val + index.val := by
        change (0 : Nat) ≠ (column.val + 1) + index.val
        intro equal
        omega0
      rw [if_neg impossible, mul_zero]
    _ = 0 := sumFin_zero

/-- Shifting both original coordinates preserves the same nilpotent cyclic matrix entry. -/
theorem shift_diagonal {dimension : Nat} {cyclic : Cyclic (Shift.matrix K (dimension + 1))}
    (value : Element cyclic) (row column : Fin dimension) :
    value.matrix row.succ column.succ = value.matrix row.castSucc column.castSucc := by
  rw [cyclic.reconstruct_entry value.matrix value.commutes row.succ column.succ,
    cyclic.reconstruct_entry value.matrix value.commutes row.castSucc column.castSucc]
  apply sumFin_congr
  intro index
  rw [cyclic.powers_eq, Shift.power_apply, Shift.power_apply]
  by_cases same : row.castSucc.val = column.castSucc.val + index.val
  · have shifted : row.succ.val = column.succ.val + index.val := by
      change row.val = column.val + index.val at same
      change row.val + 1 = (column.val + 1) + index.val
      omega0
    rw [if_pos same, if_pos shifted]
  · have different : row.succ.val ≠ column.succ.val + index.val := by
      change row.val ≠ column.val + index.val at same
      change row.val + 1 ≠ (column.val + 1) + index.val
      omega0
    rw [if_neg same, if_neg different]

/-- The zero-order distinguished entry of a two-coordinate product is its original scalar product. -/
theorem shift_mul_zero {cyclic : Cyclic (Shift.matrix K 2)} (left right : Element cyclic) :
    (left * right).matrix (0 : Fin 2) (0 : Fin 2) =
      left.matrix 0 0 * right.matrix 0 0 := by
  rw [mul_matrix, Multiplication.mul_apply, sumFin_succ, sumFin_succ]
  change left.matrix 0 0 * right.matrix 0 0 + (left.matrix 0 1 * right.matrix 1 0 + 0) = _
  have entry := shift_first_row left (0 : Fin 1)
  have first : (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
  have second : (0 : Fin 1).succ = (1 : Fin 2) := Fin.ext rfl
  rw [first, second] at entry
  rw [entry, zero_mul, zero_add, add_zero]

/-- The first-order distinguished entry of a two-coordinate product obeys the finite Leibniz law. -/
theorem shift_mul_one {cyclic : Cyclic (Shift.matrix K 2)} (left right : Element cyclic) :
    (left * right).matrix (1 : Fin 2) (0 : Fin 2) =
      left.matrix 1 0 * right.matrix 0 0 + left.matrix 0 0 * right.matrix 1 0 := by
  rw [mul_matrix, Multiplication.mul_apply, sumFin_succ, sumFin_succ]
  change left.matrix 1 0 * right.matrix 0 0 + (left.matrix 1 1 * right.matrix 1 0 + 0) = _
  have entry := shift_diagonal left (0 : Fin 1) (0 : Fin 1)
  have first : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
  have second : (0 : Fin 1).succ = (1 : Fin 2) := Fin.ext rfl
  rw [first, second] at entry
  rw [entry, add_zero]

end Element

end Purelib.Algebra.Monogenic.Cyclic

end
