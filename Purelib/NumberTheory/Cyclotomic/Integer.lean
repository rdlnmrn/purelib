module
import Purelib.Data.Nat.Division
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Integer
public import Purelib.NumberTheory.Cyclotomic.Basic
import Purelib.NumberTheory.Divisor
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
public import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
import Purelib.Polynomial.Dense.Rational.Divisibility
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Polynomial.Dense.Rational.FiniteProduct
import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic
import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Division
import Purelib.Polynomial.Dense.Rational.PowerMinusOne

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer
import Purelib.Polynomial.Dense.Rational.PowerMinusOne.Integer
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Data.Nat

open Purelib.NumberTheory

open Purelib.Polynomial

section
@[expose] public section

/-!
# Monic integer coefficients for the finite cyclotomic construction

The rational long-division factors constructed in `Cyclotomic` are
shown here to be monic and to carry executable ascending integer coefficient
lists.  The proof is a second primitive recursion over the already verified
factorization; it uses the finite monic-division theorem rather than a UFD or
root factorization.
-/

namespace Purelib.NumberTheory.Cyclotomic

open Purelib.Polynomial.Dense.Basic.DensePolynomial

namespace Integer.IntegerBridge

/-- Every positive finite cyclotomic quotient is monic. -/
theorem cyclotomic_leadingCoeff : ∀ number : Nat, 0 <
  number →
    (Cyclotomic.Basic.cyclotomic number).leadingCoeff = 1
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have factorMonic (index : Fin (previous + 2)) :
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).leadingCoeff = 1 := by
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
          exact cyclotomic_leadingCoeff
            ((previous + 1) / index.val)
            (Divisor.divisorQuotient_positive positive selected.2)
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
          exact Dense.Rational.FiniteProduct.Integer.IntegerBridge.leadingCoeff_constant_one
      have properMonic :
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)).leadingCoeff = 1 := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        exact Dense.Rational.FiniteProduct.Integer.IntegerBridge.leadingCoeff_productFin_one (previous + 2)
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1))
          (Cyclotomic.Basic.properCyclotomicFactor_nonzero (previous + 1) positive)
          factorMonic
      have stage := Cyclotomic.Basic.cyclotomic_stageSpec (previous + 1) positive
      have representedFactorization : Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1) =
          Cyclotomic.Basic.properCyclotomicProduct (previous + 1) *
            Cyclotomic.Basic.cyclotomic (previous + 1) :=
        Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
          (Dense.Rational.PowerMinusOne.powerMinusOne_normalized (previous + 1))
            (Dense.Basic.DensePolynomial.normalize_mul _ _)
          stage.factorization
      have leadingIdentity := congrArg
        (fun polynomial : Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial => polynomial.leadingCoeff)
        representedFactorization
      rw [Dense.Rational.PowerMinusOne.powerMinusOne_leadingCoeff previous,
        Dense.Basic.DensePolynomial.leadingCoeff_mul
          (Cyclotomic.Basic.properCyclotomicProduct_nonzero (previous + 1) positive)
          stage.nonzero,
        properMonic, one_mul] at leadingIdentity
      exact leadingIdentity.symm
termination_by number => number
decreasing_by all_goals exact Division.div_lt_self (by omega0) (by omega0)

/-- The proper product is monic; exposed separately for long division and
the real-cyclotomic reduction. -/
theorem cyclotomic_leadingCoeff_product (previous : Nat)
    (positive : 0 < previous + 1) :
    (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)).leadingCoeff = 1 := by
  rw [Cyclotomic.Basic.properCyclotomicProduct]
  apply Dense.Rational.FiniteProduct.Integer.IntegerBridge.leadingCoeff_productFin_one
  · exact Cyclotomic.Basic.properCyclotomicFactor_nonzero (previous + 1) positive
  · intro index
    by_cases selected :
        2 ≤ index.val ∧ index.val ∣ previous + 1
    · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
      exact cyclotomic_leadingCoeff _
        (Divisor.divisorQuotient_positive positive selected.2)
    · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
      exact Dense.Rational.FiniteProduct.Integer.IntegerBridge.leadingCoeff_constant_one

/-- Every positive finite cyclotomic quotient has integer coefficients. -/
theorem cyclotomic_integral : ∀ number : Nat, 0 < number →
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (Cyclotomic.Basic.cyclotomic number)
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have factorIntegral (index : Fin (previous + 2)) :
          Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial
            (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index) := by
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
          exact cyclotomic_integral
            ((previous + 1) / index.val)
            (Divisor.divisorQuotient_positive positive selected.2)
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
          exact Dense.Rational.IntegerCoefficients.Basic.integral_constant (Fraction.Integer.integral_of_integer 1)
      have properIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)) := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        exact Dense.Rational.FiniteProduct.Integer.IntegerBridge.integral_productFin (previous + 2)
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1)) factorIntegral
      rw [Cyclotomic.Basic.cyclotomic_succ]
      exact Dense.Rational.IntegerCoefficients.Division.divMod_quotient_integral _ _
        (Dense.Rational.PowerMinusOne.Integer.IntegerBridge.powerMinusOne_integral (previous + 1)) properIntegral
        (by
          exact cyclotomic_leadingCoeff_product previous positive)
termination_by number => number
decreasing_by all_goals exact Division.div_lt_self (by omega0) (by omega0)

end Integer.IntegerBridge

/-- Canonical executable ascending integer coefficients of `Φₙ`. -/
def Integer.cyclotomicCoefficients (number : Nat) : List Int :=
  Dense.Rational.AscendingInteger.Certificate.integerCoefficients
    (Cyclotomic.Basic.cyclotomic number)

/-- Reading back the integer coefficients recovers the positive-stage cyclotomic polynomial. -/
theorem Integer.ofAscending_cyclotomicCoefficients (number : Nat)
    (positive : 0 < number) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Cyclotomic.Integer.cyclotomicCoefficients number) =
      Cyclotomic.Basic.cyclotomic number := by
  unfold Cyclotomic.Integer.cyclotomicCoefficients
  rw [Dense.Rational.AscendingInteger.Certificate.ofAscending_integerCoefficients_eq_normalize
    _ (Cyclotomic.Integer.IntegerBridge.cyclotomic_integral number positive)]
  exact (Cyclotomic.Basic.cyclotomic_stageSpec number positive).normalized

/-- Evaluating the retained integer coefficient list agrees with rational cyclotomic evaluation. -/
@[simp] theorem Integer.eval_cyclotomicCoefficients (number : Nat)
    (positive : 0 < number) (point : Fraction.Rational) :
    Ascending.Integer.Basic.eval
        (Cyclotomic.Integer.cyclotomicCoefficients number) point =
      (Cyclotomic.Basic.cyclotomic number).eval point := by
  rw [← Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    Cyclotomic.Integer.ofAscending_cyclotomicCoefficients number positive]

/-- Coefficient list in one quotient-coordinate slot of the proper product. -/
def Integer.properCyclotomicFactorCoefficients (number : Nat)
    (divisor : Fin (number + 1)) : List Int :=
  if _selected : 2 ≤ divisor.val ∧ divisor.val ∣ number then
    Cyclotomic.Integer.cyclotomicCoefficients (number / divisor.val)
  else [1]

/-- Reading back one integer coefficient slot recovers its positive-stage proper cyclotomic factor. -/
theorem Integer.ofAscending_properCyclotomicFactorCoefficients
    (number : Nat) (positive : 0 < number)
    (divisor : Fin (number + 1)) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Cyclotomic.Integer.properCyclotomicFactorCoefficients number divisor) =
      Cyclotomic.Basic.properCyclotomicFactor number divisor := by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · rw [Cyclotomic.Integer.properCyclotomicFactorCoefficients, dif_pos selected,
      Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
    exact Cyclotomic.Integer.ofAscending_cyclotomicCoefficients _
      (Divisor.divisorQuotient_positive positive selected.2)
  · rw [Cyclotomic.Integer.properCyclotomicFactorCoefficients, dif_neg selected,
      Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
    exact Dense.Rational.AscendingInteger.Basic.ofAscending_one

/-- Ascending integer coefficients of the complete proper divisor product. -/
def Integer.properCyclotomicProductCoefficients (number : Nat) : List Int :=
  Dense.Rational.FiniteProduct.Integer.coefficientProductFin (number + 1)
    (Cyclotomic.Integer.properCyclotomicFactorCoefficients number)

/-- Reading back the integer product coefficients recovers the positive-stage proper-divisor product. -/
theorem Integer.ofAscending_properCyclotomicProductCoefficients
    (number : Nat) (positive : 0 < number) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Cyclotomic.Integer.properCyclotomicProductCoefficients number) =
      Cyclotomic.Basic.properCyclotomicProduct number := by
  rw [Cyclotomic.Integer.properCyclotomicProductCoefficients,
    Dense.Rational.FiniteProduct.Integer.ofAscending_coefficientProductFin, Cyclotomic.Basic.properCyclotomicProduct]
  apply Dense.Rational.FiniteProduct.productFin_congr
  intro divisor
  exact Cyclotomic.Integer.ofAscending_properCyclotomicFactorCoefficients number positive divisor

/-- Coefficient form of the complete finite divisor factorization of
`X^n-1`. -/
theorem Integer.cyclotomic_factorization_coefficients
    (number : Nat) (positive : 0 < number) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
          number) =
      Dense.Rational.AscendingInteger.Basic.ofAscending
        (Ascending.Integer.Basic.Certificate.mul
          (Cyclotomic.Integer.properCyclotomicProductCoefficients number)
          (Cyclotomic.Integer.cyclotomicCoefficients number)) := by
  calc
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
          number) = Dense.Rational.PowerMinusOne.powerMinusOne number :=
      Dense.Rational.PowerMinusOne.Integer.ofAscending_powerMinusOneCoefficients number
    _ = Cyclotomic.Basic.properCyclotomicProduct number * Cyclotomic.Basic.cyclotomic number :=
      Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
        (Dense.Rational.PowerMinusOne.powerMinusOne_normalized number) (Dense.Basic.DensePolynomial.normalize_mul _ _)
        (Cyclotomic.Basic.cyclotomic_stageSpec number positive).factorization
    _ = Dense.Rational.AscendingInteger.Basic.ofAscending
        (Ascending.Integer.Basic.Certificate.mul
          (Cyclotomic.Integer.properCyclotomicProductCoefficients number)
          (Cyclotomic.Integer.cyclotomicCoefficients number)) := by
      rw [Dense.Rational.AscendingInteger.Basic.ofAscending_mul,
        Cyclotomic.Integer.ofAscending_properCyclotomicProductCoefficients number positive,
        Cyclotomic.Integer.ofAscending_cyclotomicCoefficients number positive]

/-- The divisor factorization evaluates in every explicit field, including
finite characteristic, because it has already been reduced to an integer
coefficient identity. -/
theorem Integer.eval_cyclotomic_factorization_coefficients
    {K : Type*} [ExplicitField K]
    (number : Nat) (positive : 0 < number) (point : K) :
    Ascending.Integer.Basic.eval
        (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
          number) point =
      Ascending.Integer.Basic.eval
          (Cyclotomic.Integer.properCyclotomicProductCoefficients number) point *
        Ascending.Integer.Basic.eval
          (Cyclotomic.Integer.cyclotomicCoefficients number) point := by
  have transported := Dense.Rational.AscendingInteger.Certificate.eval_eq_of_ofAscending_eq
    (Cyclotomic.Integer.cyclotomic_factorization_coefficients number positive) point
  rw [Ascending.Integer.Basic.eval_mul] at transported
  exact transported

end Purelib.NumberTheory.Cyclotomic

end
