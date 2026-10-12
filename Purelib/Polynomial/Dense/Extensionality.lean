module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.RootBound

import Purelib.Tactic.QuotientFreeOmega

/-!
# Coefficient extensionality for normalized dense polynomials

Two retained normalized coefficient lists are equal when their exact dense
subtraction is zero. Aligning the original lists with zero padding reduces
the proof to structural cancellation of corresponding scalar coefficients.
-/

namespace Purelib.Polynomial.Dense.Extensionality

open Purelib.Polynomial.Dense
open Purelib.Algebra.Field
open Purelib.Data.List
open Purelib.Data.Nat

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Equal-length coefficient lists coincide when their pairwise difference trims to the empty list.

The recursive argument identifies corresponding heads before descending through the unchanged tails. -/
private theorem eq_of_subtraction_dropWhile_eq_nil
    {A : Type*} [AddCommGroup A] [DecidableEq A] :
    ∀ left right : List A,
      left.length = right.length →
      (List.zipWith (· + ·) left (right.map (-·))).dropWhile (· = 0) = [] →
      left = right
  | [], [], _, _ => rfl
  | [], _ :: _, length, _ => by
      exact Nat.noConfusion length
  | _ :: _, [], length, _ => by
      exact Nat.noConfusion length
  | left :: leftTail, right :: rightTail, length, zero => by
      have length := Nat.succ.inj length
      simp only [List.map_cons, List.zipWith_cons_cons] at zero
      by_cases headZero : left + -right = 0
      · rw [DropWhile.cons_of_true (fun value : A => decide (value = 0))
          (left + -right) _ (decide_eq_true headZero)] at zero
        have headEqual : left = right := by
          calc
            left = (left + -right) + right := by
              rw [add_assoc, neg_add_cancel, add_zero]
            _ = right := by rw [headZero, zero_add]
        rw [headEqual, eq_of_subtraction_dropWhile_eq_nil leftTail rightTail
          length zero]
      · rw [DropWhile.cons_of_false (fun value : A => decide (value = 0))
          (left + -right) _ (decide_eq_false headZero)] at zero
        cases zero

/-- Dropping leading zeros erases a prefixed zero block before trimming the remaining list.

Each retained prefix entry is zero, so its Boolean equality test selects the
recursive branch before the original remaining list is scanned. -/
private theorem dropWhile_replicate_zero_append
    {A : Type*} [Zero A] [DecidableEq A] (count : Nat) (values : List A) :
    (List.replicate count 0 ++ values).dropWhile (· = 0) =
      values.dropWhile (· = 0) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.cons_append,
        DropWhile.cons_of_true (fun value : A => decide (value = 0))
          0 _ (decide_eq_true (Eq.refl (0 : A))), inductionHypothesis]

/-- An exactly zero coefficient difference identifies two normalized dense polynomials.

The original maximum coefficient count aligns both lists with zero padding.
Trimming their pairwise difference identifies those same padded lists and then
the retained normalized coefficients. -/
public theorem normalized_eq_of_sub_isZero
    {left right : RootBound.CoefficientPolynomial K}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (differenceZero : (left - right).isZero = true) : left = right := by
  have differenceEmpty : (left - right).coeffs = [] := by
    have normalizedEmpty : (left - right).normalize.coeffs = [] := by
      unfold Basic.DensePolynomial.isZero at differenceZero
      cases coefficients : (left - right).normalize.coeffs with
      | nil => rfl
      | cons coefficient remaining =>
          rw [coefficients] at differenceZero
          exact Bool.noConfusion differenceZero
    rw [Basic.DensePolynomial.normalize_sub] at normalizedEmpty
    exact normalizedEmpty
  apply Basic.DensePolynomial.ext
  let count := max left.coeffs.length right.coeffs.length
  let leftPadded := Basic.DensePolynomial.padLeft (count - left.coeffs.length) left.coeffs
  let rightPadded := Basic.DensePolynomial.padLeft (count - right.coeffs.length) right.coeffs
  have leftLength : left.coeffs.length ≤ count := Order.le_max_left _ _
  have rightLength : right.coeffs.length ≤ count := Order.le_max_right _ _
  have paddedLength : leftPadded.length = rightPadded.length := by
    dsimp only [leftPadded, rightPadded, Basic.DensePolynomial.padLeft]
    rw [Append.length_append, Append.length_append,
      Replicate.length_replicate, Replicate.length_replicate,
      Nat.add_comm (count - left.coeffs.length), Subtraction.add_sub_of_le leftLength,
      Nat.add_comm (count - right.coeffs.length), Subtraction.add_sub_of_le rightLength]
  have rightNegCoefficients : (-right).coeffs = right.coeffs.map (-·) := by
    rw [Basic.DensePolynomial.neg_coeffs, rightNormalized]
  have rightNegLength : (-right).coeffs.length = right.coeffs.length := by
    rw [rightNegCoefficients, Map.length_map]
  have paddedNeg :
      Basic.DensePolynomial.padLeft (count - right.coeffs.length) (-right).coeffs =
        rightPadded.map (-·) := by
    rw [rightNegCoefficients]
    dsimp only [rightPadded, Basic.DensePolynomial.padLeft]
    rewrite [Map.map_append, Replicate.map_replicate, neg_zero]
    exact Eq.refl _
  have paddedDifference :
      (List.zipWith (· + ·) leftPadded (rightPadded.map (-·))).dropWhile
          (· = 0) = [] := by
    change (Basic.DensePolynomial.add left (-right)).coeffs = [] at differenceEmpty
    simp only [Basic.DensePolynomial.add] at differenceEmpty
    rw [rightNegLength] at differenceEmpty
    change
      (List.zipWith (· + ·)
        (Basic.DensePolynomial.padLeft (count - left.coeffs.length) left.coeffs)
        (Basic.DensePolynomial.padLeft (count - right.coeffs.length) (-right).coeffs)).dropWhile
          (· = 0) = [] at differenceEmpty
    rw [paddedNeg] at differenceEmpty
    exact differenceEmpty
  have paddedEqual : leftPadded = rightPadded :=
    eq_of_subtraction_dropWhile_eq_nil leftPadded rightPadded paddedLength
      paddedDifference
  dsimp only [leftPadded, rightPadded, Basic.DensePolynomial.padLeft] at paddedEqual
  have trimmedEqual := congrArg (List.dropWhile (· = (0 : K))) paddedEqual
  rw [dropWhile_replicate_zero_append,
    dropWhile_replicate_zero_append] at trimmedEqual
  have leftTrim : left.coeffs.dropWhile (· = 0) = left.coeffs := by
    exact congrArg Basic.DensePolynomial.coeffs
      leftNormalized
  have rightTrim : right.coeffs.dropWhile (· = 0) = right.coeffs := by
    exact congrArg Basic.DensePolynomial.coeffs
      rightNormalized
  rw [leftTrim, rightTrim] at trimmedEqual
  exact trimmedEqual
end Purelib.Polynomial.Dense.Extensionality
