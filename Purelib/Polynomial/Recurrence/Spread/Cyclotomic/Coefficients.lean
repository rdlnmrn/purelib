module

import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Bool.Decide
import Purelib.Data.Nat.Decide
import Purelib.Data.Nat.FiniteSum
import Purelib.Data.Nat.Division
public import Purelib.NumberTheory.Cyclotomic.Integer
import Purelib.NumberTheory.Totient.Basic
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.FiniteProduct
import Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer
public import Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Substitution
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Multiplication

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory

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

namespace Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- Dense polynomials over the constructive rational coefficient field. -/
abbrev
  CoefficientPolynomial
  :=
  Dense.Basic.DensePolynomial Fraction.Rational

/-- The executable spread-cyclotomic factor.  Index one is the endpoint
factor `s`; every index at least two is the quadratic norm of the finite
ordinary cyclotomic factor after `t = 2 - 4s`. -/
def
  spreadCyclotomicFactorCoefficients
  : Nat → List Int
  | 0 => [1]
  | 1 => [0, 1]
  | index + 2 =>
      Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadRealFactorCoefficients
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.cyclotomicCoefficients (index + 2)))

/-- The zeroth spread-cyclotomic factor is the constant one. -/
@[simp] theorem
  spreadCyclotomicFactorCoefficients_zero
  :
    Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
      0 = [1] := rfl

/-- The first spread-cyclotomic factor is the coordinate polynomial. -/
@[simp] theorem
  spreadCyclotomicFactorCoefficients_one
  :
    Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
      1 = [0, 1] := rfl

/-- Away from the endpoint, the displayed spread factor is exactly the
substituted quadratic norm. -/
theorem
  eval_spreadCyclotomicFactorCoefficients_of_two_le
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    Ascending.Integer.Basic.eval
      (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
      number) value =
      Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.cyclotomicCoefficients number))
        (2 - 4 * value) := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero => exact False.elim (by omega0)
      | succ index =>
          change
            Ascending.Integer.Basic.eval
              (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
              (index + 2)) value =
              Ascending.Integer.Basic.eval
                (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
                  (Cyclotomic.Integer.cyclotomicCoefficients
                    (index + 2))) (2 - 4 * value)
          rw
            [ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients,

              Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.eval_spreadRealFactorCoefficients]

/-- A quotient-coordinate slot for all proper non-endpoint divisors.  The
coordinate range is `0,...,n-1`; hence the exceptional quotient `1`, which
occurs at coordinate `n`, is deliberately absent. -/
def
  properSpreadCyclotomicFactorCoefficients
  (number : Nat)
    (divisor : Fin number) : List Int :=
  if _selected : 2 ≤ divisor.val ∧ divisor.val ∣ number then
    Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
      (number / divisor.val)
  else [1]

/-- Product of all proper spread factors except `C_1`. -/
def
  properSpreadCyclotomicProductCoefficients
  (number : Nat) : List Int :=
  Dense.Rational.FiniteProduct.Integer.coefficientProductFin number

      (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
      number)

/-- Totient degrees in the same proper non-endpoint quotient-coordinate
slots. -/
def
  properSpreadCyclotomicTotientSum
  (number : Nat) : Nat :=
  Data.Nat.FiniteSum.sumFinNat number fun divisor =>
    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
      Totient.Basic.totient (number / divisor.val)
    else 0

/-- The endpoint degree, all proper non-endpoint degrees, and the current
totient degree add to `n`.  This is the exact finite divisor-degree law. -/
theorem
  endpoint_add_properTotient_add_current
    (number : Nat) (twoLe : 2 ≤ number) :
    1 +
      Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicTotientSum
      number +
        Totient.Basic.totient number = number := by
  let whole : Nat → Nat := fun divisor =>
    if Data.Nat.Decide.divisibilityTest divisor number then
      Totient.Basic.totient (number / divisor)
    else 0
  let endpoint : Nat → Nat := fun divisor =>
    if Data.Nat.Decide.natEquals divisor 1 then
      Totient.Basic.totient number
    else 0
  let proper : Fin number → Nat := fun divisor =>
    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
      Totient.Basic.totient (number / divisor.val)
    else 0
  have termSplit (divisor : Fin number) :
      whole divisor.val = proper divisor + endpoint divisor.val := by
    by_cases divides : divisor.val ∣ number
    · dsimp only [whole, proper, endpoint]
      rw [show Data.Nat.Decide.divisibilityTest divisor.val number = true by
          exact (Data.Nat.Decide.divisibilityTest_eq_true _ _).2 divides]
      by_cases large : 2 ≤ divisor.val
      · have notOne : divisor.val ≠ 1 := by omega0
        have notEndpoint : Data.Nat.Decide.natEquals divisor.val 1 = false :=
          Data.Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
            notOne ((Data.Nat.Decide.natEquals_eq_true _ _).1 equal))
        have selected : 2 ≤ divisor.val ∧ divisor.val ∣ number :=
          ⟨large, divides⟩
        rewrite [if_pos rfl, if_pos selected, notEndpoint,
          if_neg (by decide : ¬(false = true)), Nat.add_zero]
        rfl
      · have positive : 0 < divisor.val := by
          by_contra notPositive
          have zero : divisor.val = 0 := Nat.eq_zero_of_not_pos notPositive
          have numberZero : number = 0 := by
            apply Nat.eq_zero_of_zero_dvd
            rw [← zero]
            exact divides
          omega0
        have one : divisor.val = 1 := by omega0
        have notSelected : ¬(2 ≤ divisor.val ∧ divisor.val ∣ number) :=
          fun selected => large selected.1
        have endpointTrue : Data.Nat.Decide.natEquals 1 1 = true :=
          (Data.Nat.Decide.natEquals_eq_true 1 1).2 rfl
        rw [if_neg notSelected, one, Data.Nat.Division.div_one]
        rewrite [if_pos rfl, endpointTrue, if_pos rfl, Nat.zero_add]
        rfl
    · dsimp only [whole, proper, endpoint]
      have notSelected : ¬(2 ≤ divisor.val ∧ divisor.val ∣ number) :=
        fun selected => divides selected.2
      have notOne : divisor.val ≠ 1 := by
        intro one
        apply divides
        rw [one]
        exact one_dvd number
      rw [show Data.Nat.Decide.divisibilityTest divisor.val number = false by
            exact Data.Bool.Decide.bool_eq_false_of_not_eq_true _ (fun truth =>
              divides ((Data.Nat.Decide.divisibilityTest_eq_true _ _).1 truth)),
        if_neg notSelected]
      have endpointFalse : Data.Nat.Decide.natEquals divisor.val 1 = false :=
        Data.Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
          notOne ((Data.Nat.Decide.natEquals_eq_true _ _).1 equal))
      rw [endpointFalse]
      rfl
  have prefixSplit :
      Data.Nat.FiniteSum.natSum number whole =
        Data.Nat.FiniteSum.sumFinNat number proper +
          Data.Nat.FiniteSum.natSum number endpoint :=
    Data.Nat.FiniteSum.natSum_eq_sumFinNat_add
      number whole endpoint proper termSplit
  have endpointSum : Data.Nat.FiniteSum.natSum number endpoint =
      Totient.Basic.totient number := by
    unfold endpoint
    rw [Data.Nat.FiniteSum.natSum_singletonWeight]
    rw [show Data.Nat.Decide.natLess 1 number = true by
      exact (Data.Nat.Decide.natLess_eq_true 1 number).2 twoLe]
    rfl
  have total := Totient.Basic.divisorQuotientTotientSum_eq number
  unfold Totient.Basic.divisorQuotientTotientSum at total
  change Data.Nat.FiniteSum.natSum (number + 1) whole = number at total
  rw [Data.Nat.FiniteSum.natSum_succ_last, prefixSplit, endpointSum] at total
  have finalDivides : Data.Nat.Decide.divisibilityTest number number = true :=
    (Data.Nat.Decide.divisibilityTest_eq_true number number).2 (dvd_refl number)
  dsimp only [whole] at total
  rw [finalDivides, if_pos rfl, Data.Nat.Division.div_self (by omega0),
    Totient.Basic.totient_one] at total
  unfold
    Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicTotientSum
  change 1 + Data.Nat.FiniteSum.sumFinNat number proper +
      Totient.Basic.totient number = number
  omega0

/-- The complete divisor product at index `n`. -/
def
  spreadCyclotomicDivisorProductCoefficients
  : Nat → List Int
  | 0 => []
  | 1 => [0, 1]
  | number + 2 =>
      Ascending.Integer.Basic.Certificate.mul
        (Ascending.Integer.Basic.Certificate.mul [0, 1]

            (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductCoefficients
            (number + 2)))

          (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
          (number + 2))

/-- Canonical constructive-rational polynomial represented by `C_n`. -/
def
  spreadCyclotomicFactorPolynomial
  (number : Nat) : CoefficientPolynomial :=
  Dense.Rational.AscendingInteger.Basic.ofAscending

      (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
      number)

/-- Canonical polynomial for the proper non-endpoint product. -/
def
  properSpreadCyclotomicProductPolynomial
  (number : Nat) : CoefficientPolynomial :=
  Dense.Rational.AscendingInteger.Basic.ofAscending

      (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductCoefficients
      number)

/-- The proper coefficient program is the corresponding finite polynomial
product. -/
theorem
  properSpreadCyclotomicProductPolynomial_eq_productFin
    (number : Nat) :

      ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductPolynomial
      number =
      Dense.Rational.FiniteProduct.productFin number fun divisor =>
        Dense.Rational.AscendingInteger.Basic.ofAscending

            (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
            number divisor) := by
  unfold
    ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductPolynomial

      ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductCoefficients
  exact Dense.Rational.FiniteProduct.Integer.ofAscending_coefficientProductFin _ _

/-- For `n >= 2`, the complete coefficient program visibly consists of the
endpoint, the proper non-endpoint product, and the current factor. -/
theorem
  ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
    (number : Nat) (twoLe : 2 ≤ number) :
    Dense.Rational.AscendingInteger.Basic.ofAscending

          (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
          number) =
      (Dense.Rational.AscendingInteger.Basic.ofAscending [0, 1] *

            ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductPolynomial
            number) *

          ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorPolynomial
          number := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero => exact False.elim (by omega0)
      | succ index =>
          change
            Dense.Rational.AscendingInteger.Basic.ofAscending
                (Ascending.Integer.Basic.Certificate.mul
                  (Ascending.Integer.Basic.Certificate.mul [0, 1]

                      (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductCoefficients
                      (index + 2)))

                    (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
                    (index + 2))) =
              (Dense.Rational.AscendingInteger.Basic.ofAscending
                    [0, 1] *
                  Dense.Rational.AscendingInteger.Basic.ofAscending

                      (ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicProductCoefficients
                      (index + 2))) *
                Dense.Rational.AscendingInteger.Basic.ofAscending

                    (ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorCoefficients
                    (index + 2))
          rw [Dense.Rational.AscendingInteger.Basic.ofAscending_mul,
            Dense.Rational.AscendingInteger.Basic.ofAscending_mul]
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Coefficients.ExerciseEightThirteen.IntegerPolynomial

end
