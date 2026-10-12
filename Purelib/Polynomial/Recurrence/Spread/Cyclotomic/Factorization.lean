module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Nat.Division
import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Algebra.Quadratic.TracePair.Norm
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.NumberTheory.Cyclotomic.Basic
import Purelib.NumberTheory.Cyclotomic.Integer
import Purelib.NumberTheory.Cyclotomic.QuadraticTrace
import Purelib.NumberTheory.Divisor
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
import Purelib.Polynomial.Ascending.Integer.Products
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Products
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.RationalIdentity
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer
import Purelib.Polynomial.Dense.Rational.PowerMinusOne.Integer
import Purelib.Polynomial.Recurrence.Lucas.Basic
import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Recurrence
public import Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Coefficients
import Purelib.Polynomial.Recurrence.Spread.Lucas

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

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

open Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Coefficients.ExerciseEightThirteen

namespace Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Factorization

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- The exceptional endpoint norm contributes exactly `4s`. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_norm_cyclotomicCoefficients_one
  (value : K) :
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.cyclotomicCoefficients 1))
        (2 - 4 * value) =
      4 * value := open Purelib in by
  have coefficientIdentity :
      Dense.Rational.AscendingInteger.Basic.ofAscending
          (Cyclotomic.Integer.cyclotomicCoefficients 1) =
        Dense.Rational.AscendingInteger.Basic.ofAscending
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            1) := by
    rw [Cyclotomic.Integer.ofAscending_cyclotomicCoefficients
        1 (by omega0),
      Dense.Rational.PowerMinusOne.Integer.ofAscending_powerMinusOneCoefficients,
      Cyclotomic.Basic.ExerciseEightThirteen.IntegerPolynomial.cyclotomic_one_eq_powerMinusOne_one]
  have pairIdentity :=
    Algebra.Quadratic.TracePair.eval_eq_of_ofAscending_eq
      coefficientIdentity (2 - 4 * value)
  calc
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.cyclotomicCoefficients 1))
        (2 - 4 * value) =
      Algebra.Quadratic.TracePair.norm (2 - 4 * value)
        (Algebra.Quadratic.TracePair.eval
          (Cyclotomic.Integer.cyclotomicCoefficients 1)
          (2 - 4 * value)) :=
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients _ _
    _ = Algebra.Quadratic.TracePair.norm (2 - 4 * value)
        (Algebra.Quadratic.TracePair.eval
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            1) (2 - 4 * value)) := by
          rw [pairIdentity]
    _ = Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            1)) (2 - 4 * value) :=
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients
          _ _).symm
    _ = 2 - Algebra.Quadratic.TracePair.lucas 1
          (2 - 4 * value) :=
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_norm_powerMinusOneCoefficients
          1 (2 - 4 * value)
    _ = 4 * value := by
      rw [Algebra.Quadratic.TracePair.lucas]
      ring0

/-- Each non-endpoint quotient slot has the same norm as its spread-factor
counterpart. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_norm_properCyclotomicFactorCoefficients
    (number : Nat) (divisor : Fin number) (value : K) :
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.properCyclotomicFactorCoefficients
            number divisor.castSucc)) (2 - 4 * value) =
      Ascending.Integer.Basic.eval
        (IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
        number divisor) value := open Purelib in by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · have selectedCast :
        2 ≤ divisor.castSucc.val ∧ divisor.castSucc.val ∣ number := by
      simpa only [Fin.val_castSucc] using selected
    rw [Cyclotomic.Integer.properCyclotomicFactorCoefficients,
      dif_pos selectedCast,
        IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
      dif_pos selected]
    have quotientTwoLe : 2 ≤ number / divisor.val :=
      Divisor.divisorQuotient_two_le
        (by omega0) selected.2 divisor.isLt
    exact

        (IntegerPolynomial.eval_spreadCyclotomicFactorCoefficients_of_two_le
        (number / divisor.val) quotientTwoLe value).symm
  · have selectedCast :
        ¬(2 ≤ divisor.castSucc.val ∧ divisor.castSucc.val ∣ number) := by
      simpa only [Fin.val_castSucc] using selected
    rw [Cyclotomic.Integer.properCyclotomicFactorCoefficients,
      dif_neg selectedCast,
        IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
      dif_neg selected,
      Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients]
    have subZero (scalar : K) : scalar - 0 = scalar := by
      exact (@SubNegMonoid.sub_eq_add_neg K
        SubtractionMonoid.toSubNegMonoid scalar 0).trans
          ((congrArg (fun value : K => scalar + value)
            (SubtractionMonoid.neg_eq_of_add 0 0 (AddZeroClass.add_zero 0))).trans
              (AddZeroClass.add_zero scalar))
    simp only [-eq_self, -iff_self, subZero,Algebra.Quadratic.TracePair.eval,
      Algebra.Quadratic.TracePair.norm,
      Algebra.Quadratic.TracePair.zero,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, Int.cast_one, mul_zero, mul_one, add_zero ]
    rfl

/-- The norm of the proper ordinary divisor product is `4s` times the
product of all proper non-endpoint spread factors. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_norm_properCyclotomicProductCoefficients
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Cyclotomic.Integer.properCyclotomicProductCoefficients number))
        (2 - 4 * value) =
      4 * value *
        Ascending.Integer.Basic.eval
          (IntegerPolynomial.properSpreadCyclotomicProductCoefficients
          number) value := by
  unfold Cyclotomic.Integer.properCyclotomicProductCoefficients

      IntegerPolynomial.properSpreadCyclotomicProductCoefficients
  rw [Dense.Rational.FiniteProduct.Integer.coefficientProductFin_succ,
    Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients_mul,
    Ascending.Integer.QuadraticTrace.Products.ExerciseEightThirteen.IntegerPolynomial.eval_norm_coefficientProductFin]
  have prefixIdentity :=
    Ascending.Integer.Products.ExerciseEightThirteen.IntegerPolynomial.eval_coefficientProductFin_congr number
    (fun divisor =>
      Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
        (Cyclotomic.Integer.properCyclotomicFactorCoefficients
          number divisor.castSucc))

      (IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
      number)
    (2 - 4 * value) value
    (fun divisor =>

        ExerciseEightThirteen.IntegerPolynomial.eval_norm_properCyclotomicFactorCoefficients
        number divisor value)
  rw [prefixIdentity]
  have lastSelected : 2 ≤ (Fin.last number).val ∧
      (Fin.last number).val ∣ number := by
    simp only [Fin.val_last]
    exact ⟨twoLe, dvd_refl number⟩
  rw [Cyclotomic.Integer.properCyclotomicFactorCoefficients,
    dif_pos lastSelected, Fin.val_last, Data.Nat.Division.div_self (by omega0),

      ExerciseEightThirteen.IntegerPolynomial.eval_norm_cyclotomicCoefficients_one]
  ring0

/-- Division-free form of the full factorization.  It is valid directly in
every explicit field, including characteristics two and four's divisors. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomic_factorization_cleared
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    4 * Basic.spreadPolynomial number value =
      4 * Ascending.Integer.Basic.eval
        (IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
        number) value := open Purelib in by
  have positive : 0 < number := by omega0
  have normFactorization :=
    Cyclotomic.QuadraticTrace.ExerciseEightThirteen.IntegerPolynomial.eval_norm_cyclotomic_factorization
    (K := K) number positive (2 - 4 * value)
  calc
    4 * Basic.spreadPolynomial number value =
        2 - Recurrence.Lucas.Basic.lucas number (2 - 4 * value) :=
      Lucas.ExerciseEightThirteen.spread_lucas_cleared number value
    _ = 2 - Algebra.Quadratic.TracePair.lucas number
          (2 - 4 * value) := by
      rw [Recurrence.Lucas.Basic.ExerciseEightThirteen.IntegerPolynomial.tracePair_lucas_eqLucas]
    _ = Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            number)) (2 - 4 * value) :=
      (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_norm_powerMinusOneCoefficients
        number (2 - 4 * value)).symm
    _ = Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.properCyclotomicProductCoefficients
              number))
          (2 - 4 * value) *
        Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.cyclotomicCoefficients number))
          (2 - 4 * value) := normFactorization
    _ = (4 * value *
          Ascending.Integer.Basic.eval
            (IntegerPolynomial.properSpreadCyclotomicProductCoefficients
            number) value) *
        Ascending.Integer.Basic.eval
          (IntegerPolynomial.spreadCyclotomicFactorCoefficients
          number) value := by
      rw
        [ExerciseEightThirteen.IntegerPolynomial.eval_norm_properCyclotomicProductCoefficients
        number twoLe value,
        ←
          IntegerPolynomial.eval_spreadCyclotomicFactorCoefficients_of_two_le
          number twoLe value]
    _ = 4 * Ascending.Integer.Basic.eval
      (IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
      number) value := by
      cases number with
      | zero => exact False.elim (by omega0)
      | succ previous =>
          cases previous with
          | zero => exact False.elim (by omega0)
          | succ index =>
              change
                4 * value *
                      Ascending.Integer.Basic.eval

                          (IntegerPolynomial.properSpreadCyclotomicProductCoefficients
                          (index + 2)) value *
                    Ascending.Integer.Basic.eval
                      (IntegerPolynomial.spreadCyclotomicFactorCoefficients
                      (index + 2))
                      value =
                  4 * Ascending.Integer.Basic.eval

                      (IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
                      (index + 2))
                    value
              rw
                [IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients,
                Ascending.Integer.Basic.eval_mul,
                Ascending.Integer.Basic.eval_mul]
              simp only [Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil,
                Algebra.Ring.IntCast.cast_zero, Int.cast_one,
                mul_zero, add_zero, zero_add, mul_one]
              ring0

section

section
/-- Cancel multiplication by four from an equality of constructive rational values. -/
private theorem
  rational_eq_of_four_mul_eq
    {left right : Fraction.Rational} (equal : 4 * left = 4 * right) : left = right := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (by
      intro equality
      exact (by decide : (4 : Nat) ≠ 0)
        (Fraction.Cast.Compatibility.natCast_injective_direct equality) :
      (4 : Fraction.Rational) ≠ 0)
  simpa only [mul_comm] using equal
end

end

/-- The general factorization as an integer coefficient identity.  This is
the characteristic-independent artifact transported below. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadCyclotomic_factorization
    (number : Nat) (positive : 0 < number) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Coefficients.ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
          number) =
      Dense.Rational.AscendingInteger.Basic.ofAscending

          (IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
          number) := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
    (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro value
  rw [Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    Coefficients.ExerciseEightThirteen.IntegerPolynomial.eval_spreadPolynomialCoefficients]
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero =>
          simp only [-eq_self, -iff_self,
            IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients,
            Basic.spreadPolynomial_one, Ascending.Integer.Basic.eval_cons,
              Ascending.Integer.Basic.eval_nil, Algebra.Ring.IntCast.cast_zero,
            Int.cast_one, mul_zero, add_zero, zero_add, mul_one]
          rfl
      | succ index =>
          apply
            Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Factorization.rational_eq_of_four_mul_eq
          exact
            ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomic_factorization_cleared
            (K := Fraction.Rational) (index + 2) (by omega0) value

/-- Exercise 8.13 for every positive finite index and every explicit field:
`S_n` is exactly the executable product of its spread-cyclotomic factors. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.exercise_8_13_general
    (number : Nat) (positive : 0 < number) (value : K) :
    Basic.spreadPolynomial number value =
      Ascending.Integer.Basic.eval
        (IntegerPolynomial.spreadCyclotomicDivisorProductCoefficients
        number) value := by
  have transported :=
    Dense.Rational.AscendingInteger.Certificate.eval_eq_of_ofAscending_eq

        (ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadCyclotomic_factorization
        number positive) value
  rw
    [Coefficients.ExerciseEightThirteen.IntegerPolynomial.eval_spreadPolynomialCoefficients]
    at transported
  exact transported
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Factorization

end
