module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Array
import Purelib.Polynomial.Recurrence.Spread.Coefficients.Formula

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Quotient

/-- The spread-array integer is the quotient coefficient printed in
Exercise 8.9.  Only this presentation needs the corresponding natural cast
to be nonzero in the coefficient field. -/
theorem spreadArrayCoefficient_eq_source_quotient
    {K : Type*} [ExplicitField K] [DecidableEq K]
    (row index : Nat) (indexBound : index < row)
    (denominatorNonzero : ((row - index : Nat) : K) ≠ 0) :
    (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (row - index) : K) =
      (row : K) / (row - index : Nat) *
        ((2 * row - 1 - index).choose index : K) := open Purelib in by
  have naturalCrossProduct :=
    Purelib.Polynomial.Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_source_cross_product row
      index indexBound
  have castCrossProduct := congrArg
    (fun coefficient : Nat => (coefficient : K)) naturalCrossProduct
  simp only [NatCast.mul] at castCrossProduct
  apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {left right factor : K} (factorNonzero
    : factor ≠ 0) (productEquality : left * factor = right * factor) =>
    (Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right (K := K) (left := left) (right := right) (factor :=
    factor) factorNonzero productEquality : left = right)) denominatorNonzero
  calc
    (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (row - index) : K) *
          (row - index : Nat) =
        (row - index : Nat) *
          (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (row - index) : K) := by ring1
    _ = (row : K) * ((2 * row - 1 - index).choose index : K) :=
      castCrossProduct
    _ = (((row : K) / (row - index : Nat)) *
          (row - index : Nat)) *
        ((2 * row - 1 - index).choose index : K) := by
      rw [ExplicitField.div_mul_cancel _ denominatorNonzero]
    _ = ((row : K) / (row - index : Nat) *
          ((2 * row - 1 - index).choose index : K)) *
        (row - index : Nat) := by ring1

open Purelib.Data.Nat in
/-- A finite descending-index quotient formula for the spread polynomial.

Each natural denominator occurring in the requested prefix must have nonzero image in the supplied explicit field. -/
theorem exercise_8_9
    {K : Type*} [ExplicitField K] [DecidableEq K]
    (row : Nat) (value : K)
    (denominatorsNonzero : ∀ index : Nat, index < row →
      ((row - index : Nat) : K) ≠ 0) :
    Recurrence.Spread.Basic.spreadPolynomial row value =
      value * FiniteSum.Prefix.prefixSum row (fun index =>
        ((row : K) / (row - index : Nat)) *
          ((2 * row - 1 - index).choose index : K) *
            (-4 * value) ^ (row - index - 1)) := by
  rw [Recurrence.Spread.Coefficients.Formula.exercise_8_9_integer_coefficients]
  unfold Recurrence.Spread.Coefficients.Formula.spreadCoefficientExpansion
  rw [FiniteSum.Prefix.prefixSum_reverse]
  rw [← FiniteSum.Prefix.prefixSum_mul_left]
  apply FiniteSum.Prefix.prefixSum_congr
  intro index indexBound
  have coefficientIndex : row - 1 - index + 1 = row - index := by
    rw [Subtraction.sub_sub]
    omega0
  have powerIndex : row - 1 - index = row - index - 1 := by
    clear coefficientIndex
    repeat rw [Subtraction.sub_sub]
    omega0
  rw [coefficientIndex, powerIndex]
  rw [spreadArrayCoefficient_eq_source_quotient row index indexBound
    (denominatorsNonzero index indexBound)]
  ring1
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Quotient

end
