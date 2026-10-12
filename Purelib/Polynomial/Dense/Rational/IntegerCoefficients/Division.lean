module
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Integer
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Division.CancelLead
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
public import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic.Integer (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

namespace Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Division

/-- An integer-coefficient rational polynomial has an integral leading coefficient. -/
theorem integral_leadingCoeff {polynomial :
  CoefficientPolynomial}
    (integral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial polynomial) :
    Fraction.Integer.IsIntegralRational polynomial.leadingCoeff := by
  rcases integral with ⟨coefficients, certificate⟩
  unfold DensePolynomial.leadingCoeff
  rw [certificate]
  have result := Dense.Rational.AscendingInteger.Certificate.ofAscending_leadingCoeff_integral coefficients
  unfold DensePolynomial.leadingCoeff at result
  rw [Dense.Rational.AscendingInteger.Basic.ofAscending_normalized] at result
  exact result

/-- Dividing an integral leading coefficient by a monic leading coefficient preserves integrality. -/
theorem integral_leadingQuotientCoefficient
    {dividend divisor : CoefficientPolynomial}
    (dividendIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial dividend)
    (divisorMonic : divisor.leadingCoeff = 1) :
    Fraction.Integer.IsIntegralRational (dividend.leadingCoeff / divisor.leadingCoeff) := open Purelib.Algebra.Field in
      by
  rcases integral_leadingCoeff dividendIntegral with ⟨integer, equality⟩
  refine ⟨integer, ?_⟩
  have inverseOne : ((1 : Fraction.Rational)⁻¹) = 1 := by
    simpa only [one_mul] using
      (ExplicitField.mul_inv_cancel (1 : Fraction.Rational)
        Fraction.Field.zero_ne_one.symm)
  rw [divisorMonic, ExplicitField.div_eq_mul_inv, inverseOne, mul_one,
    equality]

/-- The leading quotient term has integer coefficients when the dividend is integral and the divisor is monic. -/
theorem integral_leadQuotient {dividend divisor :
  CoefficientPolynomial}
    (dividendIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial dividend)
    (divisorMonic : divisor.leadingCoeff = 1) :
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (DensePolynomial.leadQuotient dividend
      divisor) := by
  unfold DensePolynomial.leadQuotient
  exact Dense.Rational.IntegerCoefficients.Basic.integral_shift _
    (Dense.Rational.IntegerCoefficients.Basic.integral_constant
      (integral_leadingQuotientCoefficient dividendIntegral divisorMonic))

/-- One monic leading-term cancellation preserves integer coefficients.

Both input polynomials have integral coefficients and the divisor leading coefficient is one. -/
theorem integral_cancelLead {dividend divisor :
  CoefficientPolynomial}
    (dividendIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial dividend)
    (divisorIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1) :
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (DensePolynomial.cancelLead dividend
      divisor) := by
  unfold DensePolynomial.cancelLead
  apply Dense.Rational.IntegerCoefficients.Basic.integral_sub dividendIntegral
  apply Dense.Rational.IntegerCoefficients.Basic.integral_shift
  exact Dense.Rational.IntegerCoefficients.Basic.integral_scale
    (integral_leadingQuotientCoefficient dividendIntegral divisorMonic)
    divisorIntegral

/-- The finite monic division loop preserves integrality of its quotient accumulator.

The current dividend, divisor and quotient must have integer coefficients, and the divisor must be monic. -/
private theorem divLoop_quotient_integral (fuel :
  Nat)
    (dividend divisor quotient : CoefficientPolynomial)
    (dividendIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial dividend)
    (divisorIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1)
    (quotientIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial quotient) :
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial
      (DensePolynomial.divLoop fuel dividend divisor quotient).quotient := by
  induction fuel generalizing dividend quotient with
  | zero => exact quotientIntegral
  | succ fuel inductionHypothesis =>
      rw [DensePolynomial.divLoop_succ]
      split
      · exact quotientIntegral
      · dsimp only
        exact inductionHypothesis (DensePolynomial.cancelLead dividend divisor)
          (quotient + DensePolynomial.leadQuotient dividend divisor)
          (integral_cancelLead dividendIntegral divisorIntegral
            divisorMonic)
          (Dense.Rational.IntegerCoefficients.Basic.integral_add quotientIntegral
            (integral_leadQuotient dividendIntegral divisorMonic))

/-- Finite dense long division by a monic integer polynomial produces an
executable integer-coefficient quotient. -/
theorem divMod_quotient_integral (dividend divisor
  : CoefficientPolynomial)
    (dividendIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial dividend)
    (divisorIntegral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1) :
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (DensePolynomial.divMod dividend
      divisor).quotient := by
  have normalizedMonic : divisor.normalize.leadingCoeff = 1 := by
    unfold DensePolynomial.leadingCoeff
    rw [DensePolynomial.normalize_normalize]
    exact divisorMonic
  exact divLoop_quotient_integral (dividend.degreeCount + 1)
    dividend.normalize divisor.normalize 0
    (Dense.Rational.IntegerCoefficients.Basic.integral_normalize dividendIntegral)
    (Dense.Rational.IntegerCoefficients.Basic.integral_normalize divisorIntegral) normalizedMonic
      Dense.Rational.IntegerCoefficients.Basic.integral_zero

end Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Division

end
