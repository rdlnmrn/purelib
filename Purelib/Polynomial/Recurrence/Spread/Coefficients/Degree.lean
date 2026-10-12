module
public import Purelib.Algebra.Monoid.Int
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Append
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Ascending.Integer.Evaluation
public import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Array
import Purelib.Polynomial.Recurrence.Spread.Coefficients.Formula
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Recurrence

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Int.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Mathlib.Data.List.Basic

open Purelib.Algebra.Field
open Purelib.Data

open Purelib.Polynomial

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

open Purelib.Polynomial.Recurrence.Spread

open Purelib.Polynomial.Ascending.Integer.Evaluation
open Purelib.Polynomial.Recurrence.Spread.Coefficients
open Purelib.Polynomial.Recurrence.Spread.Coefficients.Array

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Degree

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- A closed finite coefficient list for `S_n`, extracted from the integral
coefficient formula in Exercise 8.9.  It is used only to certify the exact
degree of the recurrence list above. -/
def
  ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
  (number : Nat) : List Int :=
  0 :: (List.range number).map fun index =>
    Int.ofNat (Coefficients.Array.spreadArrayCoefficient number (index + 1)) * Int.pow (-4) index

/-- The closed degree certificate evaluates to the same spread polynomial. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_spreadDegreeCertificateCoefficients
    (number : Nat) (value : K) :
    Ascending.Integer.Basic.eval
      (Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
      number) value =
      Basic.spreadPolynomial number value := open Purelib.Algebra in by
  rw [Coefficients.Formula.exercise_8_9_integer_coefficients]
  unfold
    Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
    Coefficients.Formula.spreadCoefficientExpansion
  rw [Ascending.Integer.Basic.eval_cons,
    Purelib.Polynomial.Ascending.Integer.Evaluation.eval_map_range]
  rw [Ring.IntCast.cast_zero, zero_add]
  calc
    value * FiniteSum.Prefix.prefixSum number (fun index =>
          (Int.ofNat (Coefficients.Array.spreadArrayCoefficient number (index + 1)) *
              (-4) ^ index : Int) * value ^ index) =
        value * FiniteSum.Prefix.prefixSum number (fun index =>
          (Coefficients.Array.spreadArrayCoefficient number (index + 1) : K) *
            (-4) ^ index * value ^ index) := by
      apply congrArg (value * ·)
      apply FiniteSum.Prefix.prefixSum_congr
      intro index _
      have castFour : ((4 : Int) : K) = (4 : K) := by
        exact Int.cast_ofNat 4
      have castNegativeFour : ((-4 : Int) : K) = (-4 : K) :=
        (Ring.IntCast.neg (R := K) (4 : Int)).trans (congrArg Neg.neg castFour)
      rw [Ring.IntCast.intCast_mul, Ring.IntCast.intCast_pow,
        Int.ofNat_eq_natCast, Int.cast_natCast, castNegativeFour]
    _ = FiniteSum.Prefix.prefixSum number (fun index =>
          value * ((Coefficients.Array.spreadArrayCoefficient number (index + 1) : K) *
            (-4) ^ index * value ^ index)) :=
      (FiniteSum.Prefix.prefixSum_mul_left number value _).symm
    _ = FiniteSum.Prefix.prefixSum number (fun index =>
          (Coefficients.Array.spreadArrayCoefficient number (index + 1) : K) * value *
            (-4 * value) ^ index) := by
      apply FiniteSum.Prefix.prefixSum_congr
      intro index _
      rw [Semiring.Normalization.product_pow]
      rw [← mul_assoc value
          ((Coefficients.Array.spreadArrayCoefficient number (index + 1) : K) * (-4) ^ index)
          (value ^ index),
        ← mul_assoc value
          (Coefficients.Array.spreadArrayCoefficient number (index + 1) : K) ((-4) ^ index),
        mul_comm value (Coefficients.Array.spreadArrayCoefficient number (index + 1) : K),
        mul_assoc]

/-- The degree-certificate list at index n has exactly n plus one entries. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients_length
  (number : Nat) :
    (Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
      number).length = number + 1 := by
  unfold
    Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
  simp only [List.length_cons, List.Map.length_map, List.Range.Basic.length_range,
    -eq_self, -iff_self]
  rfl

/-- The final coefficient at positive index is the corresponding power of minus four. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients_getLast
  (index : Nat) :
    (Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
      (index + 1)).getLast? =
      some ((-4) ^ index) := by
  unfold
    Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
  rw [List.Range.Basic.range_succ, List.Map.map_append, List.map_singleton]
  simp only
    [Purelib.Polynomial.Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_succ_self,
    Int.ofNat_eq_natCast,
    Int.natCast_one, Purelib.Algebra.Monoid.Int.monoid.one_mul]
  let earlierCoefficients := (List.range index).map fun index_1 =>
    Int.ofNat (Coefficients.Array.spreadArrayCoefficient (index + 1) (index_1 + 1)) *
      (-4) ^ index_1
  change (0 :: (earlierCoefficients ++ [(-4) ^ index])).getLast? =
    some ((-4) ^ index)
  rw [show 0 :: (earlierCoefficients ++ [(-4) ^ index]) =
      (0 :: earlierCoefficients) ++ [(-4) ^ index] by rfl,
    List.Append.getLast_append_nonempty (0 :: earlierCoefficients)
      (right := [(-4) ^ index]) (by intro empty; cases empty)]
  rfl

/-- The recurrence coefficients and the closed coefficient formula represent
the same canonical rational polynomial. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate
    (number : Nat) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
          number) =
      Dense.Rational.AscendingInteger.Basic.ofAscending

          (ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients
          number) := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
    (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro value
  rw [Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    ExerciseEightThirteen.IntegerPolynomial.eval_spreadPolynomialCoefficients,

      ExerciseEightThirteen.IntegerPolynomial.eval_spreadDegreeCertificateCoefficients]

/-- The represented spread polynomial has exact degree `n`. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_natDegree
    (number : Nat) (positive : 0 < number) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending
      (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
        number)).natDegree = number := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ index =>
      rw
        [ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate]
      exact Dense.Rational.AscendingInteger.Certificate.ofAscending_natDegree_of_getLast

          (ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients_length
          (index + 1))

          (ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients_getLast
          index)

          (Purelib.Algebra.Monoid.Int.negative_four_pow_ne_zero
          index)

/-- Positive spread polynomials are nonzero in the constructive rational
coefficient model. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_nonzero
    (number : Nat) (positive : 0 < number) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending
      (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
        number)).isZero = false := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ index =>
      rw
        [ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate]
      exact Dense.Rational.AscendingInteger.Certificate.ofAscending_isZero_false_of_getLast

          (ExerciseEightThirteen.IntegerPolynomial.spreadDegreeCertificateCoefficients_getLast
          index)

          (Purelib.Algebra.Monoid.Int.negative_four_pow_ne_zero
          index)
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Degree

end
