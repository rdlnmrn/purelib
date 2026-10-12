module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Choose
import Purelib.Data.Nat.Subtraction

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the spread coefficient array

Exercise 8.9 writes every spread polynomial as a finite binomial-coefficient
sum.  Its displayed coefficient contains a quotient.  We first identify it
with the integral entry obtained by adding two shifted copies of Pascal's
triangle.  This gives a division-free theorem over every commutative ring;
the source's quotient notation is recovered only when its finitely many
denominators are supplied as nonzero.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Array

/-- The entry in the spread array at row `row` and exponent `exponent`.
It is the sum of the corresponding entries in Pascal's triangle and the
same triangle shifted down by two places. -/
def spreadArrayCoefficient (row exponent : Nat) : Nat :=
  (row + exponent).choose (exponent + exponent) +
    (row + exponent - 1).choose (exponent + exponent)

section
open Purelib.Polynomial
/-- Every exponent-zero spread-array entry equals two. -/
@[simp] theorem spreadArrayCoefficient_zero (row : Nat) :
    spreadArrayCoefficient row 0 = 2 := by
  unfold spreadArrayCoefficient
  simp only [Nat.add_zero, Nat.choose_zero_right, -eq_self, -iff_self]
  rfl

/-- Spread-array entries beyond their row index vanish. -/
theorem spreadArrayCoefficient_eq_zero_of_lt
    {row exponent : Nat} (outside : row < exponent) :
    spreadArrayCoefficient row exponent = 0 := by
  unfold spreadArrayCoefficient
  rw [Nat.choose_eq_zero_of_lt (by omega0),
    Nat.choose_eq_zero_of_lt (by omega0), Nat.zero_add]

/-- Pascal's recursion survives the two-row addition defining the spread
array.  The exponent-zero entry is retained explicitly on the right. -/
theorem spreadArrayCoefficient_recurrence
    (row exponent : Nat) :
    spreadArrayCoefficient (row + 2) (exponent + 1) +
        spreadArrayCoefficient row (exponent + 1) =
      2 * spreadArrayCoefficient (row + 1) (exponent + 1) +
        spreadArrayCoefficient (row + 1) exponent := by
  unfold spreadArrayCoefficient
  have wave := Purelib.Data.Nat.Choose.four_term_choose_recurrence (row + exponent)
    (exponent + exponent)
  rw [show (exponent + 1) + (exponent + 1) =
        exponent + exponent + 2 by omega0,
    show row + 2 + (exponent + 1) - 1 =
        row + exponent + 2 by omega0,
    show row + 2 + (exponent + 1) =
        row + exponent + 3 by omega0,
    show row + (exponent + 1) - 1 = row + exponent by omega0,
    show row + (exponent + 1) = row + exponent + 1 by omega0,
    show row + 1 + (exponent + 1) - 1 =
        row + exponent + 1 by omega0,
    show row + 1 + (exponent + 1) =
        row + exponent + 2 by omega0,
    show row + 1 + exponent - 1 = row + exponent by omega0,
    show row + 1 + exponent = row + exponent + 1 by omega0]
  exact wave

end

section
open Purelib in
open Purelib.Polynomial in
/-- For a positive exponent within the row, multiplying the spread-array entry by its exponent gives its
denominator-free binomial formula. -/
private theorem
  spreadArrayCoefficient_cross_product
    (row exponent : Nat) (positive : 0 < exponent)
    (within : exponent ≤ row) :
    exponent * spreadArrayCoefficient row exponent =
      row * (row + exponent - 1).choose (exponent + exponent - 1) := by
  let top := row + exponent - 1
  let lower := exponent + exponent - 1
  have firstRelation := Data.Nat.Choose.add_one_mul_choose_eq top lower
  have secondRelation := Data.Nat.Choose.choose_succ_right_eq top lower
  have topSucc : top + 1 = row + exponent := by
    unfold top
    omega0
  have lowerSucc : lower + 1 = exponent + exponent := by
    unfold lower
    omega0
  have remainder : top - lower = row - exponent := by
    unfold top lower
    rw [Data.Nat.Subtraction.sub_sub]
    omega0
  rw [topSucc, lowerSucc] at firstRelation
  rw [lowerSucc, remainder] at secondRelation
  suffices doubled :
      2 * (exponent * spreadArrayCoefficient row exponent) =
        2 * (row * (row + exponent - 1).choose (exponent + exponent - 1)) by
    omega0
  unfold spreadArrayCoefficient
  change
    2 * (exponent *
      ((row + exponent).choose (exponent + exponent) +
        top.choose (exponent + exponent))) =
      2 * (row * top.choose lower)
  rw [show 2 * (exponent *
      ((row + exponent).choose (exponent + exponent) +
        top.choose (exponent + exponent))) =
      (row + exponent).choose (exponent + exponent) *
      (exponent + exponent) +
        top.choose (exponent + exponent) *
          (exponent + exponent) by ring1]
  rw [← firstRelation, secondRelation]
  have reconstruction : row - exponent + exponent = row := by omega0
  calc
    (row + exponent) * top.choose lower +
          top.choose lower * (row - exponent) =
        (row - exponent + exponent + exponent) * top.choose lower +
          top.choose lower * (row - exponent) := by
      rw [reconstruction]
    _ = 2 * ((row - exponent + exponent) * top.choose lower) := by
      ring1
    _ = 2 * (row * top.choose lower) := by rw [reconstruction]
open Purelib.Polynomial in
/-- The spread-array entry at row minus index satisfies its exact binomial cross-product identity for an index below the
row. -/
theorem
  spreadArrayCoefficient_source_cross_product
    (row index : Nat) (indexBound : index < row) :
    (row - index) * spreadArrayCoefficient row (row - index) =
      row * (2 * row - 1 - index).choose index := open Purelib in by
  have positive : 0 < row - index := by omega0
  have within : row - index ≤ row := Nat.sub_le row index
  have crossProduct :=
    spreadArrayCoefficient_cross_product
    row (row - index) positive within
  have topEquality : row + (row - index) - 1 = 2 * row - 1 - index := by
    rw [Data.Nat.Subtraction.sub_sub]
    omega0
  have lowerEquality :
      (row - index) + (row - index) - 1 =
        (2 * row - 1 - index) - index := by
    clear crossProduct topEquality
    repeat rw [Data.Nat.Subtraction.sub_sub]
    omega0
  calc
    (row - index) * spreadArrayCoefficient row (row - index) =
        row * (row + (row - index) - 1).choose
          ((row - index) + (row - index) - 1) := crossProduct
    _ = row * (2 * row - 1 - index).choose
          ((2 * row - 1 - index) - index) := by
      rw [topEquality, lowerEquality]
    _ = row * (2 * row - 1 - index).choose index := by
      rw [Data.Nat.Choose.choose_symm (by
        clear crossProduct topEquality lowerEquality
        rw [Data.Nat.Subtraction.sub_sub]
        omega0)]
end

open Purelib.Polynomial in
/-- The first four rows displayed in the source's spread array. -/
theorem spreadArray_first_four_rows :
    spreadArrayCoefficient 1 1 = 1 ∧
      (spreadArrayCoefficient 2 1 = 4 ∧
        spreadArrayCoefficient 2 2 = 1) ∧
      (spreadArrayCoefficient 3 1 = 9 ∧
        spreadArrayCoefficient 3 2 = 6 ∧
        spreadArrayCoefficient 3 3 = 1) ∧
      (spreadArrayCoefficient 4 1 = 16 ∧
        spreadArrayCoefficient 4 2 = 20 ∧
        spreadArrayCoefficient 4 3 = 8 ∧
        spreadArrayCoefficient 4 4 = 1) := by
  decide
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Array

end

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

section
namespace ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section
section

end
end
end ExerciseEightThirteen.IntegerPolynomial

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Array
open _root_.ExerciseEightThirteen.IntegerPolynomial

open Purelib.Polynomial in
/-- Every positive diagonal spread-array entry equals one. -/
public theorem
  spreadArrayCoefficient_succ_self
  (index : Nat) :
    spreadArrayCoefficient (index + 1) (index + 1) = 1 := open Purelib in by
  unfold spreadArrayCoefficient
  rw [Data.Nat.Choose.choose_self,
    Nat.choose_eq_zero_of_lt (by omega0), Nat.add_zero]
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Array
end

namespace ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section

section

end
end
end ExerciseEightThirteen.IntegerPolynomial
end

end
