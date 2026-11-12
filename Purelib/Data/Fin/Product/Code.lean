module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Remainder

open Purelib.Data.Nat

/-!
# Row-major codes for finite pairs

The original bounded coordinates determine a natural row-major code.
Ordinary division and remainder recover both coordinates directly.
-/

namespace Purelib.Data.Fin.Product.Code

/-- Division recovers the first coordinate of an original row-major pair code. -/
public theorem div_code {n : Nat} (first : Nat) (second : Fin n) :
    (first * n + second.val) / n = first := by
  have positive : 0 < n := (Nat.zero_le second.val).trans_lt second.isLt
  rewrite [Nat.mul_comm first n, Division.mul_add_div positive,
    Division.div_eq_of_lt second.isLt, Nat.add_zero]
  rfl

/-- Remainder recovers the second coordinate of an original row-major pair code. -/
public theorem mod_code {n : Nat} (first : Nat) (second : Fin n) :
    (first * n + second.val) % n = second.val := by
  rewrite [Nat.mul_comm first n, Remainder.mul_add_mod, Remainder.mod_eq_of_lt second.isLt]
  rfl

/-- The original row-major code fits the product of the two retained finite dimensions. -/
public theorem code_lt {m n : Nat} (pair : Fin m × Fin n) : pair.1.val * n + pair.2.val < m * n := by
  have row : pair.1.val * n + pair.2.val < (pair.1.val + 1) * n := by
    rewrite [Nat.succ_mul]
    exact Nat.add_lt_add_left pair.2.isLt _
  exact row.trans_le (Nat.mul_le_mul_right n (Nat.succ_le_of_lt pair.1.isLt))

/-- Retain the original pair as its bounded row-major position. -/
@[expose] public def encode {m n : Nat} (pair : Fin m × Fin n) : Fin (m * n) :=
  ⟨pair.1.val * n + pair.2.val, code_lt pair⟩

/-- A position in a finite product implies a positive column count. -/
public theorem right_positive {m n : Nat} (index : Fin (m * n)) : 0 < n := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ (index.isLt.trans_le (Nat.le_of_eq (Nat.mul_zero m)))).elim
  | succ n => exact Nat.zero_lt_succ n

/-- The row recovered by division fits the original first dimension. -/
public theorem left_lt {m n : Nat} (index : Fin (m * n)) : index.val / n < m := by
  apply Nat.lt_of_not_ge
  intro exceeded
  have lower : m * n ≤ n * (index.val / n) :=
    Nat.mul_comm (index.val / n) n ▸ Nat.mul_le_mul_right n exceeded
  have upper : n * (index.val / n) ≤ index.val :=
    Nat.le_trans (Nat.le_add_left (n * (index.val / n)) (index.val % n))
      (Nat.le_of_eq (Division.mod_add_div index.val n))
  exact Nat.not_le_of_gt index.isLt (Nat.le_trans lower upper)

/-- The column recovered by remainder fits the original second dimension. -/
public theorem right_lt {m n : Nat} (index : Fin (m * n)) : index.val % n < n :=
  Nat.mod_lt _ (right_positive index)

/-- Read the original row coordinate of a bounded row-major position. -/
@[expose] public def left {m n : Nat} (index : Fin (m * n)) : Fin m := ⟨index.val / n, left_lt index⟩

/-- Read the original column coordinate of a bounded row-major position. -/
@[expose] public def right {m n : Nat} (index : Fin (m * n)) : Fin n := ⟨index.val % n, right_lt index⟩

/-- Decoding a retained pair restores its complete original row index. -/
public theorem left_encode {m n : Nat} (pair : Fin m × Fin n) : left (encode pair) = pair.1 := by
  apply Fin.ext
  exact div_code pair.1.val pair.2

/-- Decoding a retained pair restores its complete original column index. -/
public theorem right_encode {m n : Nat} (pair : Fin m × Fin n) : right (encode pair) = pair.2 := by
  apply Fin.ext
  exact mod_code pair.1.val pair.2

/-- The recovered original coordinates identify the same bounded row-major position. -/
public theorem encode_decode {m n : Nat} (index : Fin (m * n)) : encode (left index, right index) = index := by
  apply Fin.ext
  change index.val / n * n + index.val % n = index.val
  exact (Nat.add_comm _ _).trans
    ((congrArg (fun value => index.val % n + value) (Nat.mul_comm (index.val / n) n)).trans
      (Division.mod_add_div index.val n))

/-- Encoding a finite pair in row-major order is injective.

For a pair in Fin m × Fin n, the natural code is the first coordinate times n plus the second coordinate. Division and
remainder recover the two coordinates whenever a pair exists. -/
public theorem pairCode_injective {m n : Nat} : Function.Injective
    (fun pair : Fin m × Fin n => pair.1.val * n + pair.2.val) := by
  intro first second equal
  have quotient := congrArg (fun value => value / n) equal
  have remainder := congrArg (fun value => value % n) equal
  have firstValues : first.1.val = second.1.val :=
    (div_code first.1.val first.2).symm.trans
      (quotient.trans (div_code second.1.val second.2))
  have secondValues : first.2.val = second.2.val :=
    (mod_code first.1.val first.2).symm.trans
      (remainder.trans (mod_code second.1.val second.2))
  exact Prod.ext (Fin.ext firstValues) (Fin.ext secondValues)

end Purelib.Data.Fin.Product.Code
