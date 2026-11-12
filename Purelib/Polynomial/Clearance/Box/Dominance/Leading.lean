module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Square.Symmetric.Norm
import Purelib.Geometry.Rational.Box.Subdivision
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-!
# Retained leading-term dominance on rational square boundaries

The original computed margins and radial norm estimates form boundary
certificates for the same leading monomial and lower coefficient tail.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Leading

/-- The boundary estimates certify one retained quantitative dominance margin.

The retained margin is the computed leading-term gap. Its positivity
and the pointwise boundary quadrance estimates certify the original
leading monomial and lower-tail polynomial on the same box. -/
@[expose] public def largeSquare_boundaryNormDominance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Basic.BoundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) (RootRadius.Box.largeSquareBox
        p) where
  margin := LeadingDominance.largeSquareDominanceMargin p
  positive := LeadingDominance.largeSquareDominanceMargin_pos degreePositive
  lower := by
    intro z boundary
    have bounds := RootRadius.Box.largeSquare_boundary_norm_bounds boundary
    have estimate := LeadingDominance.largeSquare_radial_dominance_margin degreePositive bounds.1
      bounds.2
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using estimate

/-- Quantitative leading-term dominance on a common positive symmetric
square.

The supplied symmetric radius is at least the coefficient-computed
radius. The record retains its computed margin and both original
polynomials, together with the bound at every boundary point. -/
@[expose] public def symmetric_boundaryNormDominance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : RootRadius.denseLargeSquareRadius p ≤ radius) :
    Basic.BoundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p)
      (Box.symmetric radius
        ((RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) where
  margin := LeadingDominance.symmetricDominanceMargin p radius
  positive := LeadingDominance.symmetricDominanceMargin_pos degreePositive radiusLe
  lower := by
    intro z boundary
    have bounds := Box.Square.Symmetric.Norm.symmetric_boundary_norm_bounds
      ((RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le boundary
    have estimate := LeadingDominance.symmetric_radial_dominance_margin degreePositive radiusLe
      bounds.1 bounds.2
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using estimate

end Purelib.Polynomial.Clearance.Box.Dominance.Leading
