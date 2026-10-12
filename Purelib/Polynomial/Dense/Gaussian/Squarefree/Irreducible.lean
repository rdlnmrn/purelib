module
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision

import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Degree
public import Purelib.Polynomial.Dense.Gaussian.Factorization.GCD
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Irreducible.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication

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

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Irreducible
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- A positive-degree irreducible Gaussian-rational polynomial is squarefree.
The derivative descent and gcd bounds are proved directly from finite
coefficient scans; no root collection or infinite-carrier argument occurs. -/
def squarefreeOfIrreducible
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (irreducible :
      Dense.Gaussian.Irreducible.Basic.IrreducibleCertificate p) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p := by
  let derivative := Dense.Gaussian.GCD.derivative p
  let result := Dense.Gaussian.GCD.extendedGCD p derivative
  have derivativeNonzero : derivative.isZero = false := by
    dsimp only [derivative]
    exact Dense.Gaussian.Derivative.Degree.derivative_isZero_false
      irreducible.nonzero irreducible.degreePositive
  have derivativeDegree : derivative.natDegree < p.natDegree := by
    dsimp only [derivative]
    exact Dense.Derivative.derivative_natDegree_lt
      irreducible.nonzero irreducible.degreePositive
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero (Or.inl irreducible.nonzero)
  have gcdProper : result.gcd.natDegree < p.natDegree :=
    (result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
  have factorization :
      (p - result.gcd * result.pFactor).isZero = true := by
    simpa only [result, derivative] using Dense.Gaussian.Factorization.GCD.gcd_factorization p derivative
  have gcdConstant := irreducible.properDivisorConstant result.gcd
    result.pFactor factorization gcdNonzero gcdProper
  exact Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD p derivative
    gcdNonzero gcdConstant

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Irreducible

end
