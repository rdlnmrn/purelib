module

public import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Subtraction
public import Mathlib.Algebra.Ring.Defs

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Nat.Choose.Pascal

/-- Compute finite binomial coefficients by Pascal recursion.

Column zero has value one, positive columns in row zero have value zero, and each
successor entry is the sum of its two preceding-row entries. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | row + 1, column + 1 =>
      choose row column + choose row (column + 1)

open Purelib.Data.Nat.Choose
/-- Column zero of Pascal's triangle has value one. -/
@[simp] theorem choose_zero_right (row : Nat) : choose row 0 = 1 := by
  cases row <;> rfl

/-- Every positive column of row zero has value zero. -/
@[simp] theorem choose_zero_succ (column : Nat) :
    choose 0 (column + 1) = 0 := rfl

/-- A successor binomial entry is the sum of its two preceding-row entries. -/
@[simp] theorem choose_succ_succ (row column : Nat) :
    choose (row + 1) (column + 1) =
      choose row column + choose row (column + 1) := rfl

/-- A binomial coefficient above the diagonal is zero.

When the requested column is strictly larger than its row, simultaneous Pascal
recursion reduces the coefficient to zero. -/
theorem choose_eq_zero_of_lt : ∀ {row column : Nat},
    row < column → choose row column = 0
  | _, 0, impossible => (Nat.not_lt_zero _ impossible).elim
  | 0, _ + 1, _ => rfl
  | row + 1, column + 1, order => by
      rw [choose_succ_succ,
        choose_eq_zero_of_lt (Nat.lt_of_succ_lt_succ order),
        choose_eq_zero_of_lt (Nat.lt_of_succ_lt order), Nat.zero_add]

/-- Every diagonal binomial coefficient has value one.

The equality follows from Pascal recursion and the vanishing entry immediately beyond
the preceding diagonal. -/
@[simp] theorem choose_self : ∀ row : Nat, choose row row = 1
  | 0 => rfl
  | row + 1 => by
      rw [choose_succ_succ, choose_self,
        choose_eq_zero_of_lt (Nat.lt_succ_self row), Nat.add_zero]
end Purelib.Data.Nat.Choose.Pascal

end

section
section
/-!
# Finite constructive binomial expansion

The bounded sum below is primitive recursion on a natural count.  The
binomial theorem is proved directly from Pascal's recursion for `Nat.choose`.
No `Finset`, infinite series, completed object, carrier enumeration, or choice
principle enters this project-owned proof.
-/

public section

namespace Purelib.Data.Nat.Choose

variable {K : Type*} [CommRing K]

/-- Every diagonal binomial coefficient has value one.

The equality follows from Pascal recursion and the vanishing entry immediately beyond
the preceding diagonal. -/
theorem choose_self : ∀ row : Nat, row.choose row = 1
  | 0 => rfl
  | row + 1 => by
      rw [Nat.choose_succ_succ, choose_self row,
        Nat.choose_succ_self, Nat.add_zero]

open Purelib.Data.Nat
/-- The binomial coefficient immediately below the diagonal equals its row index. -/
theorem choose_succ_self_right : ∀ row : Nat,
    (row + 1).choose row = row + 1
  | 0 => rfl
  | row + 1 => by
      rw [Nat.choose_succ_succ, choose_succ_self_right row,
        choose_self]

/-- Adjacent binomial rows have equal products after multiplication by their retained row and column increments.

Pascal recursion splits the successor row into its two original entries. Direct natural
multiplication and scalar addition transport the two preceding-row product identities. -/
theorem add_one_mul_choose_eq (row column : Nat) :
    (row + 1) * row.choose column =
      (row + 1).choose (column + 1) * (column + 1) := by
  induction row generalizing column with
  | zero =>
      cases column with
      | zero => rfl
      | succ column =>
          change 1 * 0 = (0 + 0) * (column + 1 + 1)
          rw [Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ row ih =>
      cases column with
      | zero =>
          have previous := ih 0
          rw [Nat.choose_zero_right] at previous
          change (row + 1) * 1 = (row + 1).choose 1 * 1 at previous
          simp only [Nat.mul_one,
            -eq_self, -iff_self] at previous
          rw [Nat.choose_zero_right]
          change (row + 1 + 1) * 1 = (row + 1 + 1).choose 1 * 1
          simp only [Nat.mul_one,
            -eq_self, -iff_self]
          rw [Nat.choose_succ_succ' (row + 1) 0, Nat.choose_zero_right,
            ← previous, Nat.add_comm 1 (row + 1)]
      | succ column =>
          calc
            (row + 2) * (row + 1).choose (column + 1) =
                (row + 1) * (row + 1).choose (column + 1) +
                  (row + 1).choose (column + 1) := Nat.succ_mul _ _
            _ = (row + 1) * (row.choose column + row.choose (column + 1)) +
                  (row + 1).choose (column + 1) :=
              congrArg (fun coefficient =>
                (row + 1) * coefficient + (row + 1).choose (column + 1))
                (Nat.choose_succ_succ' row column)
            _ = (row + 1) * row.choose column +
                  (row + 1) * row.choose (column + 1) +
                  (row + 1).choose (column + 1) :=
              congrArg (fun coefficient => coefficient +
                (row + 1).choose (column + 1))
                (Multiplication.left_distrib _ _ _)
            _ = (row + 1).choose (column + 1) * (column + 1) +
                  (row + 1).choose (column + 2) * (column + 2) +
                  (row + 1).choose (column + 1) := by
              rw [ih column, ih (column + 1)]
            _ = (row + 1).choose (column + 1) * (column + 2) +
                  (row + 1).choose (column + 2) * (column + 2) := by
              rw [Nat.mul_succ ((row + 1).choose (column + 1)) (column + 1)]
              exact (Nat.add_assoc _ _ _).trans
                ((congrArg (fun tail =>
                  (row + 1).choose (column + 1) * (column + 1) + tail)
                  (Nat.add_comm _ _)).trans (Nat.add_assoc _ _ _).symm)
            _ = ((row + 1).choose (column + 1) +
                  (row + 1).choose (column + 2)) * (column + 2) :=
              (Multiplication.right_distrib _ _ _).symm
            _ = (row + 2).choose (column + 2) * (column + 2) :=
              congrArg (fun coefficient => coefficient * (column + 2))
                (Nat.choose_succ_succ' (row + 1) (column + 1)).symm

/-- Adjacent columns in a binomial row have equal products after multiplication by their retained column and
complementary increments.

The successor-row product identity and Pascal recursion identify the whole product.
Truncated natural subtraction removes the same column product on each side, including
columns beyond the row. -/
theorem choose_succ_right_eq (row column : Nat) :
    row.choose (column + 1) * (column + 1) =
      row.choose column * (row - column) := by
  have scaled := add_one_mul_choose_eq row column
  rw [Nat.choose_succ_succ' row column,
    Multiplication.right_distrib (row.choose column) (row.choose (column + 1)) (column + 1),
    Nat.add_comm (row.choose column * (column + 1))
      (row.choose (column + 1) * (column + 1))] at scaled
  calc
    row.choose (column + 1) * (column + 1) =
        (row + 1) * row.choose column - row.choose column * (column + 1) :=
      (Subtraction.sub_eq_of_eq_add scaled).symm
    _ = (row + 1) * row.choose column - (column + 1) * row.choose column :=
      congrArg (fun product => (row + 1) * row.choose column - product)
        (Nat.mul_comm _ _)
    _ = ((row + 1) - (column + 1)) * row.choose column :=
      (Multiplication.right_sub_distrib _ _ _).symm
    _ = (row - column) * row.choose column :=
      congrArg (fun complement => complement * row.choose column)
        (Nat.succ_sub_succ row column)
    _ = row.choose column * (row - column) := Nat.mul_comm _ _

/-- Binomial coefficients are symmetric in complementary additive coordinates.

In the row left + right, choosing left and choosing right give the same coefficient.
The equality is proved directly by Pascal recursion in both coordinates. -/
theorem choose_symm_add : ∀ left right : Nat,
    (left + right).choose left = (left + right).choose right
  | 0, right => by
      simp only [Nat.zero_add, Nat.choose_zero_right,
        choose_self, -eq_self, -iff_self]
      rfl
  | left + 1, 0 => by
      simp only [Nat.add_zero, choose_self,
        Nat.choose_zero_right, -eq_self, -iff_self]
      rfl
  | left + 1, right + 1 => by
      have leftPascal :
          ((left + right + 1) + 1).choose (left + 1) =
            (left + right + 1).choose left +
              (left + right + 1).choose (left + 1) :=
        Nat.choose_succ_succ' (left + right + 1) left
      have rightPascal :
          ((left + right + 1) + 1).choose (right + 1) =
            (left + right + 1).choose right +
              (left + right + 1).choose (right + 1) :=
        Nat.choose_succ_succ' (left + right + 1) right
      have firstSymmetry := choose_symm_add left (right + 1)
      have secondSymmetry := choose_symm_add (left + 1) right
      rw [show left + (right + 1) = left + right + 1 by omega0]
        at firstSymmetry
      rw [show left + 1 + right = left + right + 1 by omega0]
        at secondSymmetry
      rw [show (left + 1) + (right + 1) =
          (left + right + 1) + 1 by omega0,
        leftPascal, rightPascal, firstSymmetry, secondSymmetry,
        Nat.add_comm]

/-- Complementary columns in a fixed binomial row have equal coefficients.

The displayed bound index ≤ row ensures that row - index is the complementary column
in the same finite row. -/
theorem choose_symm {row index : Nat} (within : index ≤ row) :
    row.choose (row - index) = row.choose index := by
  have symmetry := choose_symm_add index (row - index)
  rw [show index + (row - index) = row by omega0] at symmetry
  exact symmetry.symm
end Purelib.Data.Nat.Choose

end

end

end

section

namespace Purelib.Data.Nat.Choose
/-- Four adjacent binomial rows satisfy the paired-row wave recurrence. -/
public theorem
  four_term_choose_recurrence (top
  lower : Nat) :
    (top + 3).choose (lower + 2) +
          (top + 2).choose (lower + 2) +
        ((top + 1).choose (lower + 2) + top.choose (lower + 2)) =
      2 * ((top + 2).choose (lower + 2) +
          (top + 1).choose (lower + 2)) +
        ((top + 1).choose lower + top.choose lower) := by
  have firstMiddle :
      (top + 1).choose (lower + 1) =
        top.choose lower + top.choose (lower + 1) :=
    Nat.choose_succ_succ' top lower
  have firstUpper :
      (top + 1).choose (lower + 2) =
        top.choose (lower + 1) + top.choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' top (lower + 1)
  have secondMiddle :
      (top + 2).choose (lower + 1) =
        (top + 1).choose lower + (top + 1).choose (lower + 1) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 1) lower
  have secondUpper :
      (top + 2).choose (lower + 2) =
        (top + 1).choose (lower + 1) +
          (top + 1).choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 1) (lower + 1)
  have thirdUpper :
      (top + 3).choose (lower + 2) =
        (top + 2).choose (lower + 1) +
          (top + 2).choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 2) (lower + 1)
  omega0
end Purelib.Data.Nat.Choose
end
