module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Finite cancellation for displayed rational functions

The executable extended Euclidean algorithm is run on normalized numerator
and denominator coefficient lists.  Its displayed common factor and two
cofactors are retained together with pointwise factorization identities,
finite degree balances, and a coprimality certificate for the reduced pair.
-/

namespace Purelib.RationalFunctions.Value.Basic

open Purelib.Data in
open Purelib.Polynomial in
/-- Evidence that a displayed rational function's denominator is nonzero at the indexed point.

The numerator, denominator and Gaussian point are type parameters. The value projection evaluates this exact pair at
this exact point. -/
structure ValueAt
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
      Canonical) where
  /-- The denominator polynomial evaluates to a nonzero Gaussian rational at the indexed point. -/ denominatorNonzero :
    denominator.eval point ≠ 0

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Evaluate the retained numerator times the inverse denominator at the certified point. -/
def ValueAt.value
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {point :
      Canonical}
    (_defined : ValueAt numerator denominator point) : Canonical :=
  numerator.eval point * (denominator.eval point)⁻¹

end Purelib.RationalFunctions.Value.Basic

end
