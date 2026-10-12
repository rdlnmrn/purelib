module
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.RationalFunctions.Reduction.Basic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

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

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The normalized numerator is the product of the retained common factor and numerator cofactor. -/
private theorem numerator_factorization
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity numerator.normalize
      reduced.common reduced.numeratorReduced := by
  apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  exact reduced.euclid.pIdentity point

/-- The normalized denominator is the product of the retained common factor and denominator cofactor. -/
private theorem denominator_factorization
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity denominator.normalize
      reduced.common reduced.denominatorReduced := by
  apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  exact reduced.euclid.qIdentity point

/-- The retained reduced denominator is nonzero. -/
theorem denominatorReduced_nonzero
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.denominatorReduced.isZero = false := by
  apply Dense.Gaussian.Factorization.Identity.right_isZero_false
    (p := denominator.normalize) (left := reduced.common)
  · simpa only [DensePolynomial.isZero_normalize] using reduced.denominatorNonzero
  · exact DensePolynomial.normalize_normalize denominator
  · exact reduced.denominator_factorization

/-- A nonzero original numerator has a nonzero retained numerator cofactor. -/
theorem numeratorReduced_nonzero
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator)
    (numeratorNonzero : numerator.isZero = false) :
    reduced.numeratorReduced.isZero = false := by
  apply Dense.Gaussian.Factorization.Identity.right_isZero_false
    (p := numerator.normalize) (left := reduced.common)
  · simpa only [DensePolynomial.isZero_normalize] using numeratorNonzero
  · exact DensePolynomial.normalize_normalize numerator
  · exact reduced.numerator_factorization

/-- For a nonzero numerator, its degree is the sum of the common-factor and reduced-numerator degrees. -/
theorem numerator_degree_balance
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator)
    (numeratorNonzero : numerator.isZero = false) :
    reduced.common.natDegree + reduced.numeratorReduced.natDegree =
      numerator.natDegree := by
  have balance := Dense.Gaussian.Factorization.Identity.factor_natDegree_add
    (p := numerator.normalize) (left := reduced.common)
    (right := reduced.numeratorReduced)
    (by simpa only [DensePolynomial.isZero_normalize] using numeratorNonzero)
    (DensePolynomial.normalize_normalize numerator) reduced.common_nonzero
    (reduced.numeratorReduced_nonzero numeratorNonzero)
    reduced.numerator_factorization
  simpa only [DensePolynomial.natDegree_normalize] using balance

/-- The denominator degree is the sum of the common-factor and reduced-denominator degrees. -/
theorem denominator_degree_balance
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.common.natDegree + reduced.denominatorReduced.natDegree =
      denominator.natDegree := by
  have balance := Dense.Gaussian.Factorization.Identity.factor_natDegree_add
    (p := denominator.normalize) (left := reduced.common)
    (right := reduced.denominatorReduced)
    (by simpa only [DensePolynomial.isZero_normalize] using reduced.denominatorNonzero)
    (DensePolynomial.normalize_normalize denominator) reduced.common_nonzero
    reduced.denominatorReduced_nonzero reduced.denominator_factorization
  simpa only [DensePolynomial.natDegree_normalize] using balance
end

end ReducedPair
end Purelib.RationalFunctions.Reduction.Basic

end
