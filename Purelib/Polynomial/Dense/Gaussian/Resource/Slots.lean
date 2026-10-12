module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.Zip
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.DropWhile.Basic

/-!
# Stored coefficient counts under Gaussian polynomial arithmetic
-/

namespace Purelib.Polynomial.Dense.Gaussian.Resource.Slots

open Purelib
open Purelib.Data
open Purelib.Polynomial
open Purelib.Algebra.Polynomial.DensePolynomial

public section

/-- The stored coefficient count of a sum is bounded by the larger input count.

Both input coefficient lists are padded to their common maximum length before pairwise addition. Removing the resulting
leading zero prefix cannot increase that retained length. -/
theorem add_slots (left right : Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) :
    (left + right).coeffs.length ≤
      max left.coeffs.length right.coeffs.length := open Purelib.Polynomial in by
  let count := max left.coeffs.length right.coeffs.length
  let leftPadded := Dense.Basic.DensePolynomial.padLeft (count - left.coeffs.length) left.coeffs
  let rightPadded := Dense.Basic.DensePolynomial.padLeft (count - right.coeffs.length) right.coeffs
  have leftLength : leftPadded.length = count := by
    simp only [leftPadded, Dense.Basic.DensePolynomial.padLeft, Data.List.Append.length_append,
      Data.List.Replicate.length_replicate]
    apply Nat.Subtraction.sub_add_cancel
    change left.coeffs.length ≤ max left.coeffs.length right.coeffs.length
    rw [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_left _ _
  have rightLength : rightPadded.length = count := by
    simp only [rightPadded, Dense.Basic.DensePolynomial.padLeft, Data.List.Append.length_append,
      Data.List.Replicate.length_replicate]
    apply Nat.Subtraction.sub_add_cancel
    change right.coeffs.length ≤ max left.coeffs.length right.coeffs.length
    rw [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_right _ _
  change ((List.zipWith (· + ·) leftPadded rightPadded).dropWhile
    (· = 0)).length ≤ count
  exact (Data.List.DropWhile.length_le _ _).trans (by
    rw [Data.List.Zip.length_zipWith_of_length_eq _ _ _ (leftLength.trans rightLength.symm), leftLength])

/-- A finite addition fold preserves a common bound on stored coefficient counts.

Every input list and the initial accumulator obey the supplied common allowance. Each addition retains that allowance
through the original ordered fold. -/
theorem foldl_add_slots : ∀ (values : List
  Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial)
    (accumulator : Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) (bound : Nat),
    accumulator.coeffs.length ≤ bound →
    (∀ value ∈ values, value.coeffs.length ≤ bound) →
    (values.foldl (· + ·) accumulator).coeffs.length ≤ bound
  | [], _, _, accumulatorBound, _ => accumulatorBound
  | value :: remaining, accumulator, bound, accumulatorBound, valuesBound => by
      simp only [List.foldl_cons]
      apply Purelib.Polynomial.Dense.Gaussian.Resource.Slots.foldl_add_slots remaining
        (accumulator + value) bound
      · exact (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.add_slots accumulator value).trans
          ((Nat.Order.max_eq_natMax _ _).symm ▸
            Nat.Order.max_le accumulatorBound (valuesBound value (List.Mem.head _)))
      · intro candidate member
        exact valuesBound candidate (List.Mem.tail value member)

/-- Normalized degree count does not exceed the stored coefficient count.

Degree count removes only a leading zero prefix of the stored coefficients. The remaining coefficient list is therefore
no longer than the original one. -/
theorem degreeCount_le_coeffs_length (polynomial : Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) :
    polynomial.degreeCount ≤ polynomial.coeffs.length := open Purelib.Data in open Purelib.Polynomial in by
  unfold Dense.Basic.DensePolynomial.degreeCount
  exact Data.List.DropWhile.length_le
    (fun coefficient : Gaussian.Basic.Number => decide (coefficient = 0)) _

/-- The stored coefficient count of a product is bounded by the sum of input counts.

The original normalized multiplication retains the coefficient list whose length equals its degree count. The product
degree bound is bounded by the sum of the two stored input lengths. -/
theorem mul_slots (left right : Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) :
    (left * right).coeffs.length ≤
      left.coeffs.length + right.coeffs.length := open Purelib.Polynomial in by
  have degree := Dense.Basic.DensePolynomial.degreeCount_mul_le left right
  have normalized := Dense.Basic.DensePolynomial.normalize_mul left right
  have lengthEqual : (left * right).coeffs.length =
      (left * right).degreeCount := by
    unfold Dense.Basic.DensePolynomial.degreeCount
    rw [normalized]
  rw [lengthEqual]
  exact degree.trans ((Nat.sub_le _ _).trans
    (Nat.add_le_add (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length left)
      (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length right)))

/-- Negation does not increase the stored coefficient count.

Negation maps the retained normalized coefficient list pointwise. The original leading-prefix normalization and
map-length identities bound the resulting storage. -/
theorem neg_slots (polynomial : Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) :
    (-polynomial).coeffs.length ≤ polynomial.coeffs.length := open Purelib.Polynomial in by
  rw [Dense.Basic.DensePolynomial.neg_coeffs, Data.List.Map.length_map]
  exact Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length polynomial

end

end Purelib.Polynomial.Dense.Gaussian.Resource.Slots
