module

public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Choose
import Purelib.Algebra.NatCast
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Bounded Gaussian binomial rows

The original row terms retain their increasing first-input powers, decreasing
second-input powers and Pascal-recursive natural coefficients. Their original
finite row sum satisfies the weighted Pascal recurrence at the same indices.
-/

namespace Purelib.Algebra.Binomial.Gaussian

open Purelib.Algebra
open Purelib.Algebra.FiniteSum
open Purelib.Data
open Purelib.Data.Nat

public section

/-- Compute one Gaussian binomial term with its explicit natural coefficient.

The first input has the column exponent, the second has row minus column, and the coefficient uses the retained
Pascal-recursive choose function. -/
@[expose] def binomialTerm (x y : Gaussian.Basic.Canonical) (row column : Nat) : Gaussian.Basic.Canonical :=
  x ^ column * y ^ (row - column) * (Choose.Pascal.choose row column : Gaussian.Basic.Canonical)

/-- Sum the finite Gaussian binomial row in ascending first-input exponent order.

The bounded sum includes exactly row plus one terms, from column zero through the row. -/
@[expose] def binomialSum (x y : Gaussian.Basic.Canonical) (row : Nat) : Gaussian.Basic.Canonical :=
  Prefix.sum (Binomial.Gaussian.binomialTerm x y row) (row + 1)

/-- The first Gaussian binomial term is the second input raised to the row power. -/
theorem binomialTerm_zero (x y : Gaussian.Basic.Canonical) (row : Nat) :
    Binomial.Gaussian.binomialTerm x y row 0 = y ^ row := by
  rw [Binomial.Gaussian.binomialTerm, Choose.Pascal.choose_zero_right, Nat.sub_zero, pow_zero]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im, Nat.cast_one]
      <;> ring1

/-- The first column beyond a Gaussian binomial row has zero term. -/
theorem binomialTerm_beyond (x y : Gaussian.Basic.Canonical) (row : Nat) :
    Binomial.Gaussian.binomialTerm x y row (row + 1) = 0 := by
  rw [Binomial.Gaussian.binomialTerm, Choose.Pascal.choose_eq_zero_of_lt (Nat.lt_succ_self row)]
  change _ * (0 : Gaussian.Basic.Canonical) = 0
  exact Gaussian.Basic.mul_zero _

/-- A successor Gaussian binomial term satisfies Pascal's weighted recurrence.

For a column within the preceding row, the new term is the sum of the two neighboring terms multiplied by the
corresponding input. -/
theorem binomialTerm_pascal (x y : Gaussian.Basic.Canonical) (row column : Nat)
    (order : column ≤ row) :
    Binomial.Gaussian.binomialTerm x y (row + 1) (column + 1) =
      x * Binomial.Gaussian.binomialTerm x y row column +
        y * Binomial.Gaussian.binomialTerm x y row (column + 1) := by
  by_cases endpoint : column = row
  · subst column
    rw [Binomial.Gaussian.binomialTerm_beyond]
    simp only [Binomial.Gaussian.binomialTerm, Choose.Pascal.choose_self, Nat.sub_self,
      pow_zero, pow_succ]
    rw [Gaussian.Basic.mul_zero,
      Gaussian.Basic.add_zero]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im,
        Nat.cast_one] <;> ring1
  · have strict : column < row := Nat.lt_of_le_of_ne order endpoint
    have subtractionIdentity :
        row - column = (row - (column + 1)) + 1 := by omega
    rw [Binomial.Gaussian.binomialTerm, Binomial.Gaussian.binomialTerm, Binomial.Gaussian.binomialTerm,
      Choose.Pascal.choose_succ_succ,
      Nat.succ_sub_succ_eq_sub, pow_succ, subtractionIdentity, pow_succ,
      NatCast.add]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The next Gaussian binomial row sum multiplies the current sum by the input sum.

The bounded sums retain exactly their respective row lengths. -/
theorem binomialSum_succ (x y : Gaussian.Basic.Canonical) (row : Nat) :
    Binomial.Gaussian.binomialSum x y (row + 1) = (x + y) * Binomial.Gaussian.binomialSum x y row := by
  rw [Binomial.Gaussian.binomialSum, Binomial.Gaussian.binomialSum, Prefix.sum_succ_front,
    Binomial.Gaussian.binomialTerm_zero]
  have pascalSum :
      Prefix.sum
          (fun index => Binomial.Gaussian.binomialTerm x y (row + 1) (index + 1))
          (row + 1) =
        Prefix.sum
          (fun index =>
            x * Binomial.Gaussian.binomialTerm x y row index +
              y * Binomial.Gaussian.binomialTerm x y row (index + 1))
          (row + 1) :=
    Prefix.sum_congr_lt (row + 1)
      (fun index order =>
        Binomial.Gaussian.binomialTerm_pascal x y row index (Nat.le_of_lt_succ order))
  have shiftedEnd :
      Prefix.sum (fun index => Binomial.Gaussian.binomialTerm x y row (index + 1)) (row + 1) =
        Prefix.sum (fun index => Binomial.Gaussian.binomialTerm x y row (index + 1)) row := by
    rw [Prefix.sum_succ, Binomial.Gaussian.binomialTerm_beyond,
      Gaussian.Basic.add_zero]
  rw [pascalSum, Prefix.sum_add,
    ← Prefix.mul_sum_left x (Binomial.Gaussian.binomialTerm x y row),
    ← Prefix.mul_sum_left y
      (fun index => Binomial.Gaussian.binomialTerm x y row (index + 1)),
    shiftedEnd,
    Prefix.sum_succ_front (Binomial.Gaussian.binomialTerm x y row), Binomial.Gaussian.binomialTerm_zero, pow_succ]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

end

end Purelib.Algebra.Binomial.Gaussian

section

namespace Purelib.Algebra.Binomial.Gaussian
/-- The bounded Gaussian binomial row sum equals the power of the input sum.

Finite recursion covers every natural row without an infinite series. -/
public theorem binomial (x y : Purelib.Data.Gaussian.Basic.Canonical) : ∀ row : Nat,
    Purelib.Algebra.Binomial.Gaussian.binomialSum x y row = (x + y) ^ row
  | 0 => by
      rw [Purelib.Algebra.Binomial.Gaussian.binomialSum, Purelib.Algebra.FiniteSum.Prefix.sum_succ,
        Purelib.Algebra.FiniteSum.Prefix.sum_zero,
        Purelib.Algebra.Binomial.Gaussian.binomialTerm_zero, pow_zero, pow_zero]
      apply Purelib.Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
          Purelib.Data.Gaussian.Basic.zero_re, Purelib.Data.Gaussian.Basic.zero_im,
          Purelib.Data.Gaussian.Basic.one_re, Purelib.Data.Gaussian.Basic.one_im] <;> ring1
  | row + 1 => by
      rw [Purelib.Algebra.Binomial.Gaussian.binomialSum_succ, Purelib.Algebra.Binomial.Gaussian.binomial x y row,
        pow_succ]
      apply Purelib.Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
          Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
end Purelib.Algebra.Binomial.Gaussian
end
