module

public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Multiplication

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

namespace Purelib.Polynomial.Dense.Gaussian.Irreducible.Basic
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Finite proper-divisor formulation of irreducibility.  Every argument is a
displayed dense coefficient list, and `factorization` is a decidable zero test
on another finite coefficient list. -/
structure IrreducibleCertificate (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original polynomial is represented nonzero. -/ nonzero : p.isZero = false
  /-- The original polynomial has positive natural degree. -/ degreePositive : 0 < p.natDegree
  /-- Every displayed nonzero proper-degree divisor has degree zero.

Divisibility is witnessed by the exact zero test on the finite coefficient difference with a supplied cofactor. -/
  properDivisorConstant :
    ∀ (divisor cofactor : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial),
      (p - divisor * cofactor).isZero = true →
      divisor.isZero = false →
      divisor.natDegree < p.natDegree →
      divisor.natDegree = 0
end Purelib.Polynomial.Dense.Gaussian.Irreducible.Basic

end
