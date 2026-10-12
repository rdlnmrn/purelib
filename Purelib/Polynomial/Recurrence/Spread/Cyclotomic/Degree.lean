module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.FiniteSum
import Purelib.Data.Nat.Division
import Purelib.NumberTheory.Divisor
import Purelib.NumberTheory.Totient.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
import Purelib.Polynomial.Dense.Rational.FiniteProduct
import Purelib.Polynomial.Recurrence.Spread.Coefficients.Degree
import Purelib.Polynomial.Recurrence.Spread.Coefficients.Recurrence
public import Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Coefficients
import Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Factorization

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

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

open Purelib.Polynomial.Recurrence.Spread.Cyclotomic

namespace Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Degree

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

section

end

open Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate

/-- Every positive spread-cyclotomic factor is nonzero.  This follows
constructively from the already proved factorization and the explicit
nonzero leading coefficient of `S_n`. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorPolynomial_nonzero
    (number : Nat) (positive : 0 < number) :
    (IntegerPolynomial.spreadCyclotomicFactorPolynomial
      number).isZero = false := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero =>
          unfold
            IntegerPolynomial.spreadCyclotomicFactorPolynomial
          rw
            [IntegerPolynomial.spreadCyclotomicFactorCoefficients_one]
          exact
            Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.endpointPolynomial_nonzero
      | succ index =>
          let number := index + 2
          have twoLe : 2 ≤ number := by omega0
          cases zeroTest :
            (IntegerPolynomial.spreadCyclotomicFactorPolynomial
            number).isZero with
          | false => rfl
          | true =>
              have represented :=

                  Factorization.ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadCyclotomic_factorization
                  number (by omega0)
              have divisorShape :=

                  IntegerPolynomial.ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
                  number twoLe
              have productZero :
                  (Dense.Rational.AscendingInteger.Basic.ofAscending
                        [0, 1] *

                        IntegerPolynomial.properSpreadCyclotomicProductPolynomial
                        number) *

                      IntegerPolynomial.spreadCyclotomicFactorPolynomial
                      number = 0 :=
                Dense.Basic.DensePolynomial.mul_eq_zero_of_isZero_right
                  zeroTest
              have spreadZero :
                  Dense.Rational.AscendingInteger.Basic.ofAscending

                        (Coefficients.ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
                        number) = 0 :=
                represented.trans (divisorShape.trans productZero)
              have zeroTests := congrArg
                Dense.Basic.DensePolynomial.isZero spreadZero
              rw
                [Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_nonzero
                number (by omega0),
                Dense.Basic.DensePolynomial.isZero_zero]
                at zeroTests
              exact Bool.noConfusion zeroTests

/-- Each proper non-endpoint slot is nonzero. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicFactorPolynomial_nonzero
    (number : Nat) (positive : 0 < number) (divisor : Fin number) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending

        (IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
        number divisor)).isZero =
        false := by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · rw
      [IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
      dif_pos selected]
    exact
      ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorPolynomial_nonzero
      (number / divisor.val)
      (Divisor.divisorQuotient_positive positive selected.2)
  · rw
      [IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
      dif_neg selected]
    exact
      Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.constantOnePolynomial_nonzero

/-- The constructive spread-cyclotomic factor has exactly Euler-totient
degree, completing the degree clause of Exercise 8.13. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorPolynomial_natDegree
  :
    ∀ number : Nat, 0 < number →

        (IntegerPolynomial.spreadCyclotomicFactorPolynomial
        number).natDegree =
        Totient.Basic.totient number := open Purelib in by
  intro number
  induction number using Nat.strong_induction_on with
  | h number inductionHypothesis =>
      intro positive
      cases number with
      | zero => exact False.elim ((Nat.not_lt_zero 0) positive)
      | succ previous =>
          cases previous with
          | zero =>
              unfold
                IntegerPolynomial.spreadCyclotomicFactorPolynomial
              rw
                [IntegerPolynomial.spreadCyclotomicFactorCoefficients_one,
                Totient.Basic.totient_one]
              exact
                Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.endpointPolynomial_natDegree
          | succ index =>
              let number := index + 2
              have numberPositive : 0 < number := by omega0
              have twoLe : 2 ≤ number := by omega0
              let slotPolynomial : Fin number → (Dense.Basic.DensePolynomial Fraction.Rational) := fun divisor =>
                Dense.Rational.AscendingInteger.Basic.ofAscending

                    (IntegerPolynomial.properSpreadCyclotomicFactorCoefficients
                    number divisor)
              have slotNonzero (divisor : Fin number) :
                  (slotPolynomial divisor).isZero = false := by
                exact
                  ExerciseEightThirteen.IntegerPolynomial.properSpreadCyclotomicFactorPolynomial_nonzero
                  number numberPositive divisor
              have slotDegree (divisor : Fin number) :
                  (slotPolynomial divisor).natDegree =
                    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
                      Totient.Basic.totient (number / divisor.val)
                    else 0 := by
                by_cases selected :
                    2 ≤ divisor.val ∧ divisor.val ∣ number
                · unfold slotPolynomial
                  rw
                    [IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
                    dif_pos selected, if_pos selected]
                  exact inductionHypothesis (number / divisor.val)
                    (Purelib.Data.Nat.Division.div_lt_self numberPositive (by omega0))
                    (Divisor.divisorQuotient_positive
                      numberPositive selected.2)
                · unfold slotPolynomial
                  rw
                    [IntegerPolynomial.properSpreadCyclotomicFactorCoefficients,
                    dif_neg selected, if_neg selected]
                  exact
                    Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.constantOnePolynomial_natDegree
              have properNonzero :

                    (IntegerPolynomial.properSpreadCyclotomicProductPolynomial
                    number).isZero =
                    false := by
                rw
                  [IntegerPolynomial.properSpreadCyclotomicProductPolynomial_eq_productFin]
                exact Dense.Rational.FiniteProduct.productFin_nonzero
                  number slotPolynomial slotNonzero
              have properDegree :

                    (IntegerPolynomial.properSpreadCyclotomicProductPolynomial
                    number).natDegree =

                      IntegerPolynomial.properSpreadCyclotomicTotientSum
                      number := by
                rw
                  [IntegerPolynomial.properSpreadCyclotomicProductPolynomial_eq_productFin,
                  Dense.Rational.FiniteProduct.natDegree_productFin
                    number slotPolynomial slotNonzero]
                unfold
                  IntegerPolynomial.properSpreadCyclotomicTotientSum
                apply Data.Nat.FiniteSum.sumFinNat_congr
                intro divisor
                exact slotDegree divisor
              have currentNonzero :=

                  ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicFactorPolynomial_nonzero
                  number numberPositive
              have endpointProperNonzero :
                  (Dense.Rational.AscendingInteger.Basic.ofAscending
                        [0, 1] *

                        IntegerPolynomial.properSpreadCyclotomicProductPolynomial
                        number).isZero =
                    false :=
                Dense.Basic.DensePolynomial.isZero_mul_eq_false

                    Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.endpointPolynomial_nonzero
                    properNonzero
              have represented :=

                  (Factorization.ExerciseEightThirteen.IntegerPolynomial.ofAscending_spreadCyclotomic_factorization
                  number numberPositive).trans

                      (IntegerPolynomial.ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
                      number twoLe)
              have degreeIdentity := congrArg
                Dense.Basic.DensePolynomial.natDegree represented
              rw
                [Coefficients.Degree.ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_natDegree
                number numberPositive,
                Dense.Basic.DensePolynomial.natDegree_mul
                  endpointProperNonzero currentNonzero,
                Dense.Basic.DensePolynomial.natDegree_mul

                    Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.endpointPolynomial_nonzero
                    properNonzero,

                  Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.endpointPolynomial_natDegree,
                  properDegree] at degreeIdentity
              have totalDegree :=

                  IntegerPolynomial.endpoint_add_properTotient_add_current
                  number twoLe
              change

                  (IntegerPolynomial.spreadCyclotomicFactorPolynomial
                  number).natDegree =
                  Totient.Basic.totient number
              omega0

end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Degree

end
