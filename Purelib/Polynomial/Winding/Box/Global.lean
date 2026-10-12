module

import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Coordinate
import Purelib.Polynomial.Clearance.Box.Boundary.Leading
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Clearance.Box.Dominance.Leading
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Leading
import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-!
# Degree winding on coefficient-computed rational squares

The retained finite leading/tail split transfers leading-monomial winding
to the original polynomial on every sufficiently large symmetric square.
-/

namespace Purelib.Polynomial.Winding.Box.Global

/-- The raw constructive winding of every positive-degree dense polynomial
on its coefficient-computed square is four times its finite natural degree.

Positive degree gives a normalized leading/lower split and a positive
boundary margin on the computed square. The original finite winding
transfer preserves the leading-monomial degree count. -/
public theorem quadrupledBoxWinding_largeSquare_eq_degree
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Winding.Box.Basic.quadrupledBoxWinding p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
      (4 : Int) * p.natDegree := by
  have transfer :=
    Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p)
      (Clearance.Box.Boundary.Leading.leadingMonomial_largeSquare_boundaryClearance degreePositive)
      (Clearance.Box.Dominance.Leading.largeSquare_boundaryNormDominance degreePositive)
  have decomposition :=
    Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eq_normalize degreePositive
  calc
    Winding.Box.Basic.quadrupledBoxWinding p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
        Winding.Box.Basic.quadrupledBoxWinding p.normalize (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) :=
      (Winding.Box.Basic.quadrupledBoxWinding_normalize p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)).symm
    _ = Winding.Box.Basic.quadrupledBoxWinding
          (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p +
            Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p)
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) := by rw [decomposition]
    _ = Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) :=
      transfer
    _ = (4 : Int) * p.natDegree :=
      Winding.Box.Leading.quadrupledBoxWinding_leadingMonomial degreePositive

/-- All three finite winding normalizations recover the positive dense
degree on the computed constructive square.

The raw winding equality fixes one retained integer reading. Dividing
that reading by two and four yields the doubled and ordinary winding
conventions for the same positive degree. -/
public theorem largeSquare_winding_eq_degree
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Winding.Box.Basic.quadrupledBoxWinding p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
        (4 : Int) * p.natDegree ∧
      Winding.Box.Basic.doubledBoxWinding p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
        (2 : Int) * p.natDegree ∧
      Winding.Box.Basic.boxWinding p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) = p.natDegree := by
  have raw := Winding.Box.Global.quadrupledBoxWinding_largeSquare_eq_degree degreePositive
  refine ⟨raw, ?_, ?_⟩
  · rw [Winding.Box.Basic.doubledBoxWinding, raw]
    omega
  · rw [Winding.Box.Basic.boxWinding, raw]
    omega

/-- A polynomial has raw winding four times its degree on every positive
symmetric square at least as large as its computed coefficient radius.

The radius is at least the coefficient-computed positive radius.
The leading/lower split has quantitative boundary dominance on this
same symmetric square, preserving the finite degree count. -/
public theorem quadrupledBoxWinding_symmetric_eq_degree
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius) :
    Winding.Box.Basic.quadrupledBoxWinding p
        (Box.symmetric radius
          ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
      (4 : Int) * p.natDegree := by
  let radiusPositive := (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe
  let box := Box.symmetric radius radiusPositive.le
  have proper : box.Proper := by
    change -radius < radius ∧ -radius < radius
    have reflected := Fraction.Order.Arithmetic.neg_lt_neg_direct radiusPositive
    have zeroNegation : -(0 : Fraction.Rational) = 0 := by ring1
    rewrite [zeroNegation] at reflected
    exact ⟨reflected.trans radiusPositive, reflected.trans radiusPositive⟩
  have leadingClearance :
      Clearance.Box.Boundary.Basic.BoundaryClearance
        (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p) box := by
    have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
    have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
    exact Clearance.Box.Boundary.Basic.BoundaryClearance.mul
      (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance leadingNonzero box)
      (by
        simpa only [box] using
          Clearance.Box.Boundary.Coordinate.coordinatePositivePower_symmetric_boundaryClearance
            radiusPositive (p.natDegree - 1))
  have transfer :=
    Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) box proper
      leadingClearance (Clearance.Box.Dominance.Leading.symmetric_boundaryNormDominance degreePositive radiusLe)
  have decomposition := Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eq_normalize
    degreePositive
  calc
    Winding.Box.Basic.quadrupledBoxWinding p box = Winding.Box.Basic.quadrupledBoxWinding p.normalize box :=
      (Winding.Box.Basic.quadrupledBoxWinding_normalize p box).symm
    _ = Winding.Box.Basic.quadrupledBoxWinding
          (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p +
            Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p) box := by
      rw [decomposition]
    _ = Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p) box :=
      transfer
    _ = (4 : Int) * p.natDegree :=
      Winding.Box.Leading.quadrupledBoxWinding_leadingMonomial_symmetric
        degreePositive radiusPositive

/-- On every sufficiently large positive symmetric square, the raw winding
of a nonzero polynomial is four times its natural degree, including the
constant case where both sides are zero.

The polynomial is nonzero and the radius exceeds its computed bound.
Positive degree uses the leading/lower split; degree zero retains the
nonzero constant and its zero winding. -/
public theorem quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (nonzero : p.isZero = false)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius) :
    Winding.Box.Basic.quadrupledBoxWinding p
        (Box.symmetric radius
          ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
      (4 : Int) * p.natDegree := by
  by_cases degreeZero : p.natDegree = 0
  · have normalizedConstant :
        p.normalize = Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff :=
      Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
    calc
      Winding.Box.Basic.quadrupledBoxWinding p
          (Box.symmetric radius
            ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
          Winding.Box.Basic.quadrupledBoxWinding p.normalize
            (Box.symmetric radius
              ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) :=
        (Winding.Box.Basic.quadrupledBoxWinding_normalize p _).symm
      _ = Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff)
            (Box.symmetric radius
              ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
        rw [normalizedConstant]
      _ = 0 := Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
        (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero) _
      _ = (4 : Int) * p.natDegree := by rw [degreeZero]; rfl
  · exact Winding.Box.Global.quadrupledBoxWinding_symmetric_eq_degree
      (Nat.pos_of_ne_zero degreeZero) radiusLe

end Purelib.Polynomial.Winding.Box.Global
