module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)
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

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A nonzero displayed denominator and retained Euclidean data for the normalized polynomial pair.

The Euclidean result supplies the common factor, reduced cofactors and their Bézout coefficients, together with the
factorization and normalization certificates. -/
structure ReducedPair
    (numerator denominator : CoefficientPolynomial) where
  /-- The original displayed denominator is not the zero polynomial. -/ denominatorNonzero : denominator.isZero = false
  /-- The retained Bézout result for the normalized numerator and denominator. -/ euclid :
    Dense.GCD.BezoutResult numerator.normalize denominator.normalize

constructive_injectivity ReducedPair

namespace ReducedPair

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Read the retained common polynomial factor from the Euclidean result. -/
def common
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) : (DensePolynomial
      Canonical) :=
  reduced.euclid.gcd

/-- Read the retained numerator cofactor after common-factor cancellation. -/
def numeratorReduced
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) : (DensePolynomial
      Canonical) :=
  reduced.euclid.pFactor

/-- Read the retained denominator cofactor after common-factor cancellation. -/
def denominatorReduced
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) : (DensePolynomial
      Canonical) :=
  reduced.euclid.qFactor

/-- Read the Bézout coefficient multiplying the reduced numerator. -/
def numeratorCoefficient
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) : (DensePolynomial
      Canonical) :=
  reduced.euclid.factorLeft

/-- Read the Bézout coefficient multiplying the reduced denominator. -/
def denominatorCoefficient
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) : (DensePolynomial
      Canonical) :=
  reduced.euclid.factorRight

end

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The retained common factor is already normalized. -/
theorem common_normalized
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.common.normalize = reduced.common :=
  reduced.euclid.normalized

/-- The retained numerator cofactor is already normalized. -/
theorem numeratorReduced_normalized
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.numeratorReduced.normalize = reduced.numeratorReduced :=
  reduced.euclid.pFactorNormalized

/-- The retained denominator cofactor is already normalized. -/
theorem denominatorReduced_normalized
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.denominatorReduced.normalize = reduced.denominatorReduced :=
  reduced.euclid.qFactorNormalized

end

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Every numerator evaluation factors as the common-factor evaluation times the reduced numerator evaluation. -/
theorem numerator_eval
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) (point : Canonical) :
    numerator.eval point =
      reduced.common.eval point * reduced.numeratorReduced.eval point := by
  rw [← DensePolynomial.eval_normalize numerator point]
  exact reduced.euclid.pIdentity point

/-- Every denominator evaluation factors as the common-factor evaluation times the reduced denominator evaluation. -/
theorem denominator_eval
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) (point : Canonical) :
    denominator.eval point =
      reduced.common.eval point * reduced.denominatorReduced.eval point := by
  rw [← DensePolynomial.eval_normalize denominator point]
  exact reduced.euclid.qIdentity point

/-- The retained Bézout coefficients combine the reduced cofactors to one at every Gaussian point. -/
theorem reduced_identity
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) (point : Canonical) :
    1 = reduced.numeratorCoefficient.eval point *
          reduced.numeratorReduced.eval point +
        reduced.denominatorCoefficient.eval point *
          reduced.denominatorReduced.eval point :=
  reduced.euclid.factorIdentity point

end

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The retained common factor is nonzero because the original denominator is nonzero. -/
theorem common_nonzero
    {numerator denominator : CoefficientPolynomial}
    (reduced : Reduction.Basic.ReducedPair numerator denominator) :
    reduced.common.isZero = false :=
  reduced.euclid.nonzero (Or.inr (by
    simpa only [DensePolynomial.isZero_normalize] using reduced.denominatorNonzero))
end ReducedPair
end Purelib.RationalFunctions.Reduction.Basic

end
