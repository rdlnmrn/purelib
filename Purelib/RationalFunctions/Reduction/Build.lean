module
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Reduction.Basic

section
@[expose] public section

/-!
# Finite cancellation for displayed rational functions

The executable extended Euclidean algorithm is run on normalized numerator
and denominator coefficient lists.  Its displayed common factor and two
cofactors are retained together with pointwise factorization identities,
finite degree balances, and a coprimality certificate for the reduced pair.
-/

namespace Purelib.RationalFunctions.Reduction.Build

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Compute a retained cancellation certificate for the normalized polynomial pair.

The original denominator is explicitly nonzero. Extended Euclidean computation supplies the common factor, reduced
cofactors and all retained Bézout evidence. -/
def reduce
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    Reduction.Basic.ReducedPair numerator denominator where
  denominatorNonzero := denominatorNonzero
  euclid := Dense.GCD.extendedGCD
    numerator.normalize denominator.normalize
end Purelib.RationalFunctions.Reduction.Build

end
