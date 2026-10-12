module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Parity-aware finite square-factor reduction

An exact multiplicity basis gives `p = s * s * q`: half of each
multiplicity goes into `s`, and only odd multiplicities remain in `q`.
The scalar stays in `q`, without extracting a square root in the coefficient
field.  This is not the squarefree radical, which would retain even factors.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

set_option genInjectivity false in
/-- Cached executable factors and the finite coefficient identity relating
them to the original input representation, including unnormalized inputs. -/
structure Reduction (polynomial :
  CoefficientPolynomial) where
  /-- The cached finite coefficient polynomial whose square is removed from the source. -/ squareFactor :
    CoefficientPolynomial
  /-- The cached residual polynomial retaining the scalar and odd factor multiplicities. -/ radicand :
    CoefficientPolynomial
  /-- The retained square factor is nonzero. -/ squareFactorNonzero : squareFactor.isZero = false
  /-- The retained radicand is nonzero. -/ radicandNonzero : radicand.isZero = false
  /-- The cached square-factor table is normalized. -/ squareFactorNormalized : squareFactor.normalize = squareFactor
  /-- The cached radicand table is normalized. -/ radicandNormalized : radicand.normalize = radicand
  /-- The executable squarefree certificate belongs to the exact retained radicand. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate radicand
  /-- The finite zero-difference certificate relates the original source to the square of its retained factor times its
    retained radicand. -/ identity : Dense.Gaussian.Factorization.Identity.ProductIdentity polynomial
    (squareFactor * squareFactor) radicand

constructive_injectivity Reduction

namespace Reduction

/-- The source evaluation equals the square of the retained square-factor value times the retained radicand value. -/
theorem evalIdentity {polynomial :
  CoefficientPolynomial}
    (reduction : Reduction polynomial) (point : Gaussian.Basic.Canonical) :
    polynomial.eval point = reduction.squareFactor.eval point *
      reduction.squareFactor.eval point * reduction.radicand.eval point := by
  have identity := Dense.Gaussian.Factorization.Identity.eval_factorization reduction.identity point
  simpa only [DensePolynomial.eval_mul] using identity

/-- Literal equality of normalized coefficient lists, derived from the
finite zero-difference certificate without any carrier-wide extensionality. -/
theorem normalizedIdentity {polynomial
  : CoefficientPolynomial}
    (reduction : Reduction polynomial) :
    polynomial.normalize =
      (reduction.squareFactor * reduction.squareFactor) * reduction.radicand := by
  apply Dense.Extensionality.normalized_eq_of_sub_isZero
    (DensePolynomial.normalize_normalize polynomial) (DensePolynomial.normalize_mul _ _)
  apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point _
  simpa only [DensePolynomial.eval_normalize, DensePolynomial.eval_mul] using
    reduction.evalIdentity point

/-- Exact degree loss under square-factor removal, including degree-zero
radicands and non-normalized representations of the source. -/
theorem degreeBalance {polynomial :
  CoefficientPolynomial}
    (reduction : Reduction polynomial) (nonzero : polynomial.isZero =
      false) :
    polynomial.natDegree =
      2 * reduction.squareFactor.natDegree + reduction.radicand.natDegree := by
  have normalizedIdentity : Dense.Gaussian.Factorization.Identity.ProductIdentity polynomial.normalize
      (reduction.squareFactor * reduction.squareFactor) reduction.radicand := by
    apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    simpa only [DensePolynomial.eval_normalize, DensePolynomial.eval_mul] using
      reduction.evalIdentity point
  have balance := Dense.Gaussian.Factorization.Identity.factor_natDegree_add
    (show polynomial.normalize.isZero = false by
        simpa only [DensePolynomial.isZero_normalize]
          using nonzero)
    (DensePolynomial.normalize_normalize polynomial)
    (DensePolynomial.isZero_mul_eq_false reduction.squareFactorNonzero reduction.squareFactorNonzero)
    reduction.radicandNonzero normalizedIdentity
  rw [DensePolynomial.natDegree_mul reduction.squareFactorNonzero reduction.squareFactorNonzero,
    DensePolynomial.natDegree_normalize] at balance
  omega

end Reduction
end Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

end
