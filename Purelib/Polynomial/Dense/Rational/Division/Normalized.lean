module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Division.CancelLead
public import Purelib.Polynomial.Dense.Rational.Divisibility

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive finite cyclotomic factors

Ordinary cyclotomic factors are constructed here without roots of unity or
Mathlib's noncomputable cyclotomic hierarchy.  The coefficient program uses
the project's canonical rational records and finite dense long division.
The proof follows the elementary square-free divisor argument: previously
constructed pairwise-coprime factors all divide `X^n-1`, so their product
does too, and the next executable quotient is exact.
-/

namespace Purelib.Polynomial.Dense.Rational.Division.Normalized

/-- Executable long-division quotients stay normalized. -/
private theorem divLoop_quotient_normalized (fuel : Nat)
    (dividend divisor quotient : Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial)
    (quotientNormalized : quotient.normalize = quotient) :
    (DensePolynomial.divLoop fuel dividend divisor quotient).quotient.normalize =
      (DensePolynomial.divLoop fuel dividend divisor quotient).quotient := by
  induction fuel generalizing dividend quotient with
  | zero => exact quotientNormalized
  | succ fuel inductionHypothesis =>
      rw [DensePolynomial.divLoop_succ]
      split
      · exact quotientNormalized
      · dsimp only
        exact inductionHypothesis (DensePolynomial.cancelLead dividend divisor)
          (quotient + DensePolynomial.leadQuotient dividend divisor)
            (DensePolynomial.normalize_add _ _)

/-- The quotient returned by rational dense long division is normalized. -/
theorem divMod_quotient_normalized (dividend divisor :
  Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial) :
    (DensePolynomial.divMod dividend divisor).quotient.normalize =
      (DensePolynomial.divMod dividend divisor).quotient := by
  exact divLoop_quotient_normalized (dividend.degreeCount + 1)
    dividend.normalize divisor.normalize 0 DensePolynomial.normalize_zero
end Purelib.Polynomial.Dense.Rational.Division.Normalized

end
