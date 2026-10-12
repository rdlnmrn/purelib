module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
public import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

section
@[expose] public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Power

/-- Coprimality with one right factor extends to every displayed finite
power of that factor. -/
def polynomialPowerRightCoprime
    {p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (pNonzero : p.isZero = false)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q) : ∀ exponent : Nat,
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate p
      (Dense.Gaussian.Power.polynomialPower q exponent)
  | 0 =>
      Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight
        pNonzero
  | exponent + 1 =>
      Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight pNonzero
        coprime (polynomialPowerRightCoprime pNonzero coprime exponent)

end Purelib.Polynomial.Dense.Gaussian.Coprime.Power

end
