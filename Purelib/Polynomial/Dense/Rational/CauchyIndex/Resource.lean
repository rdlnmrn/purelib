module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Source-computed field-operation budget for constructing one signed chain
and evaluating every emitted member at both endpoints. -/
def cauchyIndexFieldOperationBudget (p q :
  Dense.Rational.Basic.CoordinatePolynomial) : Nat :=
  let workingP := id p
  let workingQ := id q
  Dense.Rational.SignedRemainder.Resource.chainRoundSteps (max workingQ.degreeCount workingP.degreeCount) *
      (workingP.degreeCount + 1) +
    4 * (workingP.degreeCount + 1) *
      max workingQ.coeffs.length workingP.coeffs.length
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- A natural envelope for endpoint evaluation of the retained signed-remainder chain.

The denominator and numerator use their original order in the chain construction, and the endpoint is read through its
exact rational representation. -/
def endpointMagnitudeEnvelope (p q :
  Dense.Rational.Basic.CoordinatePolynomial)
    (point : Fraction.Rational) : Nat :=
  Dense.Rational.SignedRemainder.Resource.workingEndpointMagnitudeEnvelope (id q)
    (id p) (Fraction.Basic.ofRational point)
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource

end
