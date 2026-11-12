module

public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Polynomial.Dense.ZeroMultiplicity
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.Data.List.Replicate
import Purelib.Tactic.QuotientFreeOmega

/-!
# Zero-root multiplicity under original coefficient reversal

The same original reciprocal coefficient table has constant equal to the
source leader. Reversal removes exactly the source's actual zero-root
multiplicity from its represented degree.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Reciprocal

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.List

/-- The original reciprocal table has no zero root because its constant is the original nonzero leader. -/
theorem reversed_zeroMultiplicity (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) :
    (reversed polynomial).zeroMultiplicity = 0 :=
  DensePolynomial.zeroMultiplicity_eq_zero_of_eval_zero_nonzero _ (by
    rewrite [reversed_origin]
    exact DensePolynomial.leadingCoeff_ne_zero nonzero)

/-- Coefficient reversal removes exactly the original zero-root multiplicity from the represented degree. -/
theorem reversed_degree_zeroMultiplicity (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) :
    (reversed polynomial).natDegree + polynomial.zeroMultiplicity = polynomial.natDegree := by
  have coreNormalized := DensePolynomial.zeroCore_normalized nonzero
  have sameCount : (reversed polynomial).degreeCount = polynomial.zeroCore.degreeCount := by
    change (polynomial.normalize.coeffs.reverse.dropWhile (· = 0)).length =
      polynomial.zeroCore.normalize.coeffs.length
    rewrite [coreNormalized]
    exact (Reverse.length_reverse _).symm
  have coreSize : polynomial.zeroCore.coeffs.length = polynomial.zeroCore.degreeCount := by
    change _ = polynomial.zeroCore.normalize.coeffs.length
    rewrite [coreNormalized]
    rfl
  have counts := congrArg List.length (DensePolynomial.zeroCore_coefficients polynomial)
  rewrite [Append.length_append, Replicate.length_replicate, coreSize, ← sameCount] at counts
  have sourceCount := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  have targetCount := DensePolynomial.natDegree_add_one_eq_degreeCount (reversed_nonzero nonzero)
  change _ + _ = polynomial.degreeCount at counts
  omega0

end Purelib.Polynomial.Dense.Gaussian.Reciprocal

end
