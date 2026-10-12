module
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Substitution.Affine
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Exact affine reparameterization of the finite Cauchy index

Affine substitution maps the actual signed Euclidean chain coefficient by
coefficient.  The endpoint evaluation lists therefore agree exactly.  The
result includes negative slopes, reversed intervals, zero coordinate
polynomials, common polynomial factors, and endpoint zeros.
-/

namespace Purelib.RootIsolation.Sturm

open Purelib.Polynomial.Dense.Rational.Substitution.Affine (subst subst_isZero subst_degreeCount subst_remainder
  subst_neg subst_eval)

end Purelib.RootIsolation.Sturm

section
open Purelib.Polynomial.Dense.Rational.Substitution.Affine (subst subst_isZero subst_degreeCount subst_remainder
  subst_neg subst_eval)

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation.Affine

open _root_.Purelib.RootIsolation.Sturm
/-- Evaluate an affinely substituted list at the original parameter.

This gives exactly the list of original polynomial values at the affine image of that parameter. -/
private theorem
  affine_evaluations (origin
  slope point : Fraction.Rational) :
    ∀ (chain : List Purelib.Polynomial.Dense.Rational.Basic.CoordinatePolynomial),
      ((chain.map fun polynomial => subst polynomial origin slope).map fun polynomial => polynomial.eval point) =
        chain.map (fun polynomial => polynomial.eval (origin + slope * point))
  | [] => rfl
  | polynomial :: remaining => by
      simp only [List.map_cons]
      rw [Dense.Rational.Substitution.Affine.subst_eval,
        affine_evaluations origin
        slope point remaining]
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation.Affine
end

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation.Affine

open Purelib.Polynomial.Dense.Rational.Substitution.Affine (subst subst_isZero subst_degreeCount subst_remainder
  subst_neg subst_eval)

/-- Affine substitution transports endpoint variation to the affine image of the point.

This evaluation identity also holds for zero slope. -/
theorem endpointVariation2_affine (chain :
  List Dense.Rational.Basic.CoordinatePolynomial) (origin slope point : Fraction.Rational) :
    Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 (chain.map fun polynomial => subst polynomial
      origin slope) point =
      Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 chain (origin + slope * point) := by
  unfold Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
  rw [affine_evaluations]
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation.Affine

end
