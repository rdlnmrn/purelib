module
import Purelib.Data.Nat.Multiplication
public import Purelib.Data.Nat.Choose
public import Purelib.Data.Nat.Factorial.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
public section

/-! Data Nat Choose Factorial and its finite structural certificates. -/

namespace Purelib.Data.Nat.Choose.Factorial

open Purelib.Data.Nat

/-- Multiply a binomial coefficient by complementary factorials to recover the row
factorial.

For column ≤ row, the project's Pascal coefficient times column! times (row -
column)! equals row!. The proof uses finite Pascal recursion and natural
multiplication. -/
theorem choose_mul_factorials : ∀ (row column : Nat), column ≤ row →
    Choose.Pascal.choose row column * Factorial.Basic.factorial column * Factorial.Basic.factorial (row - column) =
      Factorial.Basic.factorial row
  | 0, 0, _ => rfl
  | 0, column + 1, order => (Nat.not_succ_le_zero column order).elim
  | row + 1, 0, _ => by
      rewrite [Choose.Pascal.choose_zero_right, Factorial.Basic.factorial_zero, Nat.mul_one,
        Nat.sub_zero, Nat.one_mul]
      exact Eq.refl _
  | row + 1, column + 1, order => by
      have columnLe : column ≤ row := Nat.le_of_succ_le_succ order
      by_cases boundary : column = row
      · subst column
        rewrite [Choose.Pascal.choose_self, Nat.sub_self, Factorial.Basic.factorial_zero,
          Nat.mul_one, Nat.one_mul]
        exact Eq.refl _
      · have columnLt : column < row := Nat.lt_of_le_of_ne columnLe boundary
        have successorLe : column + 1 ≤ row := columnLt
        have leftIdentity := Data.Nat.Choose.Factorial.choose_mul_factorials row column columnLe
        have rightIdentity := Data.Nat.Choose.Factorial.choose_mul_factorials row (column + 1) successorLe
        have subtractionIdentity :
            row - column = (row - (column + 1)) + 1 := by omega
        have leftTerm :
            Choose.Pascal.choose row column * Factorial.Basic.factorial (column + 1) *
                Factorial.Basic.factorial (row - column) =
              (column + 1) * Factorial.Basic.factorial row := by
          rw [Factorial.Basic.factorial_succ]
          calc
            Choose.Pascal.choose row column * (Factorial.Basic.factorial column * (column + 1)) *
                Factorial.Basic.factorial (row - column) =
                (Choose.Pascal.choose row column * Factorial.Basic.factorial column *
                  Factorial.Basic.factorial (row - column)) * (column + 1) := by ring1
            _ = Factorial.Basic.factorial row * (column + 1) := by rw [leftIdentity]
            _ = (column + 1) * Factorial.Basic.factorial row := Nat.mul_comm _ _
        have rightTerm :
            Choose.Pascal.choose row (column + 1) * Factorial.Basic.factorial (column + 1) *
                Factorial.Basic.factorial (row - column) =
              (row - column) * Factorial.Basic.factorial row := by
          conv_lhs =>
            rw [subtractionIdentity, Factorial.Basic.factorial_succ]
          calc
            Choose.Pascal.choose row (column + 1) * Factorial.Basic.factorial (column + 1) *
                (Factorial.Basic.factorial (row - (column + 1)) *
                  (row - (column + 1) + 1)) =
                (Choose.Pascal.choose row (column + 1) * Factorial.Basic.factorial (column + 1) *
                  Factorial.Basic.factorial (row - (column + 1))) *
                    (row - (column + 1) + 1) := by ring1
            _ = Factorial.Basic.factorial row * (row - (column + 1) + 1) := by
              rw [rightIdentity]
            _ = Factorial.Basic.factorial row * (row - column) := by
              rw [subtractionIdentity]
            _ = (row - column) * Factorial.Basic.factorial row := Nat.mul_comm _ _
        rw [Choose.Pascal.choose_succ_succ, Nat.succ_sub_succ_eq_sub,
          Purelib.Data.Nat.Multiplication.right_distrib, Purelib.Data.Nat.Multiplication.right_distrib, leftTerm,
            rightTerm, Factorial.Basic.factorial_succ]
        calc
          (column + 1) * Factorial.Basic.factorial row +
              (row - column) * Factorial.Basic.factorial row =
              ((column + 1) + (row - column)) * Factorial.Basic.factorial row := by
                exact (Multiplication.right_distrib _ _ _).symm
          _ = (row + 1) * Factorial.Basic.factorial row := by
            congr 1
            omega
          _ = Factorial.Basic.factorial row * (row + 1) := Nat.mul_comm _ _
end Purelib.Data.Nat.Choose.Factorial

end
