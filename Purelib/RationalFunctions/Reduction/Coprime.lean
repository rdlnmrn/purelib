module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.RationalFunctions.Reduction.Basic
import Purelib.RationalFunctions.Reduction.Nonzero
public import Purelib.RationalFunctions.Reduction.Factorization

section
@[expose] public section

/-!
# Finite cancellation for displayed rational functions

The executable extended Euclidean algorithm is run on normalized numerator
and denominator coefficient lists.  Its displayed common factor and two
cofactors are retained together with pointwise factorization identities,
finite degree balances, and a coprimality certificate for the reduced pair.
-/

namespace Purelib.RationalFunctions.Reduction.Basic
namespace ReducedPair

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Construct the coprimality certificate of the retained reduced numerator and denominator.

Use their stored Bézout coefficients and exact reduced identity, with nonzeroness of the denominator cofactor. -/
def coprime
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate reduced.numeratorReduced
      reduced.denominatorReduced :=
  Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity
    reduced.numeratorReduced reduced.denominatorReduced
    (Or.inr reduced.denominatorReduced_nonzero)
    reduced.numeratorCoefficient reduced.denominatorCoefficient
    reduced.reduced_identity
end ReducedPair
end Purelib.RationalFunctions.Reduction.Basic

end
