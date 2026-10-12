module
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Affine
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation.Affine
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Polynomial.Dense.Rational.Substitution.Affine

/-!
# Exact affine reparameterization of the finite Cauchy index

Affine substitution maps the actual signed Euclidean chain coefficient by
coefficient.  The endpoint evaluation lists therefore agree exactly.  The
result includes negative slopes, reversed intervals, zero coordinate
polynomials, common polynomial factors, and endpoint zeros.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Affine

open Purelib.Data.Rat
open Purelib.Polynomial

public section

open Purelib.Polynomial.Dense.Rational.Substitution.Affine (subst subst_isZero subst_degreeCount subst_remainder
  subst_neg subst_eval)

/-- Exact Cauchy-index invariance under an invertible affine parameter change.

The nonzero slope preserves the retained signed Euclidean chain and transports
its two endpoint variations. Coordinate polynomials may vanish or share factors. -/
theorem cauchyIndex2_affine (first second : Dense.Rational.Basic.CoordinatePolynomial) (origin slope left right :
  Fraction.Rational)
    (nonzero : slope ≠ 0) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (subst first origin slope) (subst second origin slope) left
      right =
      Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 first second (origin + slope * left) (origin + slope * right)
        := by
  unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  rw [Dense.Rational.SignedRemainder.Affine.signedRemainderChain_affine second first origin slope nonzero]
  rw [Dense.Rational.SignedRemainder.Variation.Affine.endpointVariation2_affine,
    Dense.Rational.SignedRemainder.Variation.Affine.endpointVariation2_affine]

end

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Affine
