module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Dominance.Leading
public import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Algebra.Group

/-!
# Boundary clearance at a retained coefficient radius

The original finite leading-term dominance supplies quantitative clearance
on the same computed or sufficiently large symmetric rational square.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.RootRadius

/-- Coefficient-computed positive clearance for the original polynomial on
the complete large-square boundary.

Positive degree supplies leading-term clearance and a quantitative
boundary dominance margin on the computed square. Their retained
certificate gives clearance for the exact normalized leading/lower sum. -/
@[expose] public def largeSquare_boundaryClearance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Clearance.Box.Boundary.Basic.BoundaryClearance p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) := by
  have sumClearance :=
    Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p)
      (Clearance.Box.Dominance.Leading.largeSquare_boundaryNormDominance degreePositive)
  have decomposition :=
    Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eq_normalize degreePositive
  apply Clearance.Box.Boundary.Basic.BoundaryClearance.ofNormalize
  simpa only [decomposition] using sumClearance

/-- A polynomial has a coefficient-computed positive clearance on every
positive symmetric square at least as large as its own large-square radius.
This is the clearance companion to `quadrupledBoxWinding_symmetric_eq_degree`
and lets finitely many polynomials share one outer boundary.

The positive-degree polynomial and sufficiently large symmetric radius
retain leading-term clearance and a quantitative margin on that same
boundary. Normalization transfers the certificate to the original polynomial. -/
@[expose] public def symmetric_boundaryClearance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius) :
    Clearance.Box.Boundary.Basic.BoundaryClearance p
      (Box.symmetric radius
        ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
  let radiusPositive := (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe
  let box := Box.symmetric radius radiusPositive.le
  have proper : box.Proper := by
    change -radius < radius ∧ -radius < radius
    have reflected := Fraction.Order.Arithmetic.neg_lt_neg_direct radiusPositive
    have zeroNegation : -(0 : Fraction.Rational) = 0 :=
      (Negation.subNegZeroMonoid (G := Fraction.Rational)).neg_zero
    rewrite [zeroNegation] at reflected
    exact ⟨reflected.trans radiusPositive, reflected.trans radiusPositive⟩
  have sumClearance :=
    Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) box proper
      (Clearance.Box.Dominance.Leading.symmetric_boundaryNormDominance degreePositive radiusLe)
  have decomposition := Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eq_normalize
    degreePositive
  apply Clearance.Box.Boundary.Basic.BoundaryClearance.ofNormalize
  simpa only [box, decomposition] using sumClearance

/-- Every displayed nonzero polynomial has positive boundary clearance on a
sufficiently large symmetric square.  The degree-zero branch is handled by
its exact normalized constant; no positive-degree hypothesis is hidden in
the public statement.

The nonzero polynomial may have zero or positive degree. The constant
case retains its nonzero coefficient; the positive-degree case uses
leading-term dominance at the supplied sufficiently large radius. -/
@[expose] public def symmetric_boundaryClearance_of_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (nonzero : p.isZero = false)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius) :
    Clearance.Box.Boundary.Basic.BoundaryClearance p
      (Box.symmetric radius
        ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
  by_cases degreeZero : p.natDegree = 0
  · apply Clearance.Box.Boundary.Basic.BoundaryClearance.ofNormalize
    have normalizedConstant :
        p.normalize = Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff :=
      Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
    rw [normalizedConstant]
    exact Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
      (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero) _
  · exact Clearance.Box.Boundary.RootRadius.symmetric_boundaryClearance (Nat.pos_of_ne_zero degreeZero)
      radiusLe

end Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
