module
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Factorization.GCD
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The pointwise identity computed by extended Euclid certifies a finite
coefficient factorization after checking only the bounded candidate list of
the displayed difference. -/
theorem gcd_factorization
    (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    let result := Dense.Gaussian.GCD.extendedGCD p q
    (p - result.gcd * result.pFactor).isZero = true := by
  let result := Dense.Gaussian.GCD.extendedGCD p q
  apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point _
  rw [Dense.Basic.DensePolynomial.eval_mul]
  exact result.pIdentity point
end Purelib.Polynomial.Dense.Gaussian.Factorization.GCD

end
