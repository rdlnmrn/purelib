module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Witness
import Purelib.Data.Rat.Fraction.Order.PositiveMul
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Reduction

/-- Numerator after the finite Euclidean program removes the common gcd. -/
def reducedNumerator (numerator denominator :
  CoordinatePolynomial) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.GCD.leftFactor numerator denominator

/-- Denominator after the finite Euclidean program removes the common gcd. -/
def reducedDenominator (numerator denominator :
  CoordinatePolynomial) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.GCD.rightFactor numerator denominator

/-- The quotient factors returned by extended Euclid retain an explicit
Bézout identity, in denominator--numerator order. -/
def reducedPairCoprime
    (numerator denominator : CoordinatePolynomial) :
    CoprimeCertificate (reducedDenominator
      numerator denominator)
      (reducedNumerator numerator denominator) where
  left := Dense.GCD.factorRightCoefficient numerator denominator
  right := Dense.GCD.factorLeftCoefficient numerator denominator
  identity := by
    intro parameter
    have identity := Dense.GCD.reducedFactors_eval_identity
      numerator denominator parameter
    calc
      1 =
          (Dense.GCD.factorLeftCoefficient numerator denominator).eval
              parameter *
              (reducedNumerator numerator denominator).eval parameter +
            (Dense.GCD.factorRightCoefficient numerator denominator).eval
              parameter *
              (reducedDenominator numerator denominator).eval parameter := by
        simpa only [reducedNumerator, reducedDenominator]
          using identity
      _ =
          (Dense.GCD.factorRightCoefficient numerator denominator).eval
              parameter *
              (reducedDenominator numerator denominator).eval parameter +
            (Dense.GCD.factorLeftCoefficient numerator denominator).eval
              parameter *
              (reducedNumerator numerator denominator).eval parameter :=
        Fraction.Field.add_comm _ _

/-- A nonzero original numerator has a represented nonzero reduced
numerator factor. -/
theorem reducedNumerator_isZero_false
    {numerator denominator : CoordinatePolynomial}
    (nonzero : numerator.isZero = false) :
    (reducedNumerator numerator denominator).isZero = false := by
  cases factorZero : (reducedNumerator numerator denominator).isZero with
  | false => rfl
  | true =>
      let parameter := Dense.Rational.Nonzero.Witness.nonzeroParameter numerator nonzero
      have factorEvalZero :
          (reducedNumerator numerator denominator).eval parameter = 0 :=
        Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero factorZero parameter
      have identity :=
        (Dense.GCD.extendedGCD numerator denominator).pIdentity
          parameter
      change numerator.eval parameter =
        (Dense.GCD.gcd numerator denominator).eval parameter *
          (reducedNumerator numerator denominator).eval parameter at identity
      rw [factorEvalZero,
        Fraction.Field.mul_zero_direct] at identity
      exact (Dense.Rational.Nonzero.Witness.eval_nonzeroParameter numerator nonzero identity).elim

/-- A nonzero original denominator has a represented nonzero reduced
denominator factor. -/
theorem reducedDenominator_isZero_false
    {numerator denominator : CoordinatePolynomial}
    (nonzero : denominator.isZero = false) :
    (reducedDenominator numerator denominator).isZero = false := by
  cases factorZero : (reducedDenominator numerator denominator).isZero with
  | false => rfl
  | true =>
      let parameter := Dense.Rational.Nonzero.Witness.nonzeroParameter denominator nonzero
      have factorEvalZero :
          (reducedDenominator numerator denominator).eval parameter = 0 :=
        Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero factorZero parameter
      have identity :=
        (Dense.GCD.extendedGCD numerator denominator).qIdentity
          parameter
      change denominator.eval parameter =
        (Dense.GCD.gcd numerator denominator).eval parameter *
          (reducedDenominator numerator denominator).eval parameter at identity
      rw [factorEvalZero,
        Fraction.Field.mul_zero_direct] at identity
      exact (Dense.Rational.Nonzero.Witness.eval_nonzeroParameter denominator nonzero identity).elim

/-- A nonzero denominator value remains nonzero after gcd reduction.

The exact factor identity rules out a zero value of the retained quotient factor. -/
theorem reducedDenominator_eval_ne_zero
    {numerator denominator : CoordinatePolynomial} {parameter : Fraction.Rational}
    (nonzero : denominator.eval parameter ≠ 0) :
    (reducedDenominator numerator denominator).eval parameter ≠ 0 := by
  intro factorZero
  have identity :=
    (Dense.GCD.extendedGCD numerator denominator).qIdentity parameter
  change denominator.eval parameter =
    (Dense.GCD.gcd numerator denominator).eval parameter *
      (reducedDenominator numerator denominator).eval parameter at identity
  rw [factorZero, Fraction.Field.mul_zero_direct] at identity
  exact nonzero identity

/-- A supplied Bézout identity prevents the executable common gcd from
vanishing at any displayed coordinate. -/
theorem gcd_eval_ne_zero_of_coprime
    {numerator denominator : CoordinatePolynomial} {parameter : Fraction.Rational}
    (coprime : CoprimeCertificate denominator numerator) :
    (Dense.GCD.gcd numerator denominator).eval parameter ≠ 0 := by
  intro gcdZero
  have numeratorIdentity := Dense.GCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := Dense.GCD.rightFactor_eval_identity
    numerator denominator parameter
  rw [gcdZero, Fraction.Field.zero_mul_direct]
    at numeratorIdentity denominatorIdentity
  have identity := coprime.identity parameter
  rw [denominatorIdentity, numeratorIdentity,
    Fraction.Field.mul_zero_direct,
    Fraction.Field.mul_zero_direct,
    Fraction.Field.zero_add] at identity
  exact Fraction.Field.zero_ne_one identity.symm

/-- Removing the executable common gcd preserves a strict negative product.
The proof uses only the two displayed factor identities and the pointwise
nonvanishing supplied by finite Bézout data. -/
theorem reduced_product_neg_of_original
    {numerator denominator : CoordinatePolynomial} {parameter : Fraction.Rational}
    (coprime : CoprimeCertificate denominator numerator)
    (negative : numerator.eval parameter * denominator.eval parameter < 0) :
    (reducedNumerator numerator denominator).eval parameter *
        (reducedDenominator numerator denominator).eval parameter < 0 := by
  let gcdValue :=
    (Dense.GCD.gcd numerator denominator).eval parameter
  let numeratorValue :=
    (reducedNumerator numerator denominator).eval parameter
  let denominatorValue :=
    (reducedDenominator numerator denominator).eval parameter
  have gcdNonzero : gcdValue ≠ 0 :=
    gcd_eval_ne_zero_of_coprime coprime
  have gcdSquarePositive : 0 < gcdValue * gcdValue :=
    by simpa only [pow_two] using Fraction.Order.Arithmetic.exact_rational_sq_pos gcdNonzero
  have numeratorIdentity := Dense.GCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := Dense.GCD.rightFactor_eval_identity
    numerator denominator parameter
  have factored :
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) < 0 := by
    calc
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) =
          numerator.eval parameter * denominator.eval parameter := by
        dsimp only [gcdValue, numeratorValue, denominatorValue,
          reducedNumerator, reducedDenominator]
        rw [numeratorIdentity, denominatorIdentity]
        ring1
      _ < 0 := negative
  rcases lt_trichotomy (numeratorValue * denominatorValue) 0 with
      reducedNegative | reducedZero | reducedPositive
  · exact reducedNegative
  · rw [reducedZero, Fraction.Field.mul_zero_direct] at factored
    exact (lt_irrefl 0 factored).elim
  · have productPositive := Fraction.Order.Arithmetic.mul_pos_direct
      gcdSquarePositive reducedPositive
    exact (lt_asymm productPositive factored).elim

/-- Removing the executable common gcd likewise preserves a strict positive
product. -/
theorem reduced_product_pos_of_original
    {numerator denominator : CoordinatePolynomial} {parameter : Fraction.Rational}
    (coprime : CoprimeCertificate denominator numerator)
    (positive : 0 < numerator.eval parameter * denominator.eval parameter) :
    0 < (reducedNumerator numerator denominator).eval parameter *
      (reducedDenominator numerator denominator).eval parameter := by
  let gcdValue :=
    (Dense.GCD.gcd numerator denominator).eval parameter
  let numeratorValue :=
    (reducedNumerator numerator denominator).eval parameter
  let denominatorValue :=
    (reducedDenominator numerator denominator).eval parameter
  have gcdNonzero : gcdValue ≠ 0 :=
    gcd_eval_ne_zero_of_coprime coprime
  have gcdSquarePositive : 0 < gcdValue * gcdValue :=
    by simpa only [pow_two] using Fraction.Order.Arithmetic.exact_rational_sq_pos gcdNonzero
  have numeratorIdentity := Dense.GCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := Dense.GCD.rightFactor_eval_identity
    numerator denominator parameter
  have factored : 0 <
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) := by
    calc
      0 < numerator.eval parameter * denominator.eval parameter := positive
      _ = (gcdValue * gcdValue) *
          (numeratorValue * denominatorValue) := by
        dsimp only [gcdValue, numeratorValue, denominatorValue,
          reducedNumerator, reducedDenominator]
        rw [numeratorIdentity, denominatorIdentity]
        ring1
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct factored
    gcdSquarePositive.le
end Purelib.Polynomial.Dense.Rational.Pair.Reduction

end
