module

import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Coordinate
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Coordinate.Power
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Winding.Box.Coordinate
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-!
# Winding of the retained leading monomial

The nonzero leading coefficient and original coordinate-power factor
retain the same finite product winding and positive dense degree.
-/

namespace Purelib.Polynomial.Winding.Box.Leading

/-- The leading monomial has raw winding four times the positive dense
degree on the coefficient-computed square.

Positive degree supplies a nonzero leading coefficient. Its constant
factor has zero winding, while the retained coordinate power contributes
four times the same natural degree on the computed square. -/
public theorem quadrupledBoxWinding_leadingMonomial
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
      (4 : Int) * p.natDegree := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  have product :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff)
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1))
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p)
      (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance leadingNonzero
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
      (by
        simpa only [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox] using
          Clearance.Box.Boundary.Coordinate.coordinatePositivePower_symmetric_boundaryClearance
            (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p) (p.natDegree - 1))
  have powerWinding := Winding.Box.Coordinate.Power.quadrupledBoxWinding_coordinatePositivePower
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p) (p.natDegree - 1)
  change Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff *
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1))
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) = (4 : Int) * p.natDegree
  rw [product,
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant leadingNonzero
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)]
  rw [show Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1))
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
        (4 : Int) * (((p.natDegree - 1 : Nat) : Int) + 1) by
      simpa only [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox] using powerWinding]
  omega

/-- Both normalized winding conventions inherit the exact leading-monomial
degree.

The raw winding is four times the positive natural degree. The original
doubled and ordinary winding operations divide that same retained
integer by their respective normalization factors. -/
public theorem leadingMonomial_largeSquare_normalization
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Winding.Box.Basic.doubledBoxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) =
        (2 : Int) * p.natDegree ∧
      Winding.Box.Basic.boxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) = p.natDegree := by
  have raw := Winding.Box.Leading.quadrupledBoxWinding_leadingMonomial degreePositive
  constructor
  · rw [Winding.Box.Basic.doubledBoxWinding, raw]
    omega
  · rw [Winding.Box.Basic.boxWinding, raw]
    omega

/-- The leading monomial has degree winding on every positive symmetric
square, independently of the polynomial-specific computed radius.

The symmetric radius is strictly positive and the degree is positive.
The nonzero constant factor and retained coordinate-power factor give
the same degree winding on that supplied square. -/
public theorem quadrupledBoxWinding_leadingMonomial_symmetric
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational} (radiusPositive : 0 < radius) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
        (Box.symmetric radius radiusPositive.le) =
      (4 : Int) * p.natDegree := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  have product :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff)
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1))
      (Box.symmetric radius radiusPositive.le)
      (by
        change -radius < radius ∧ -radius < radius
        have reflected := Fraction.Order.Arithmetic.neg_lt_neg_direct radiusPositive
        have zeroNegation : -(0 : Fraction.Rational) = 0 := by ring1
        rewrite [zeroNegation] at reflected
        exact ⟨reflected.trans radiusPositive, reflected.trans radiusPositive⟩)
      (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance leadingNonzero _)
      (Clearance.Box.Boundary.Coordinate.coordinatePositivePower_symmetric_boundaryClearance radiusPositive _)
  have powerWinding := Winding.Box.Coordinate.Power.quadrupledBoxWinding_coordinatePositivePower
    radiusPositive (p.natDegree - 1)
  change Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff *
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1))
      (Box.symmetric radius radiusPositive.le) =
        (4 : Int) * p.natDegree
  rw [product,
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant leadingNonzero _]
  rw [powerWinding]
  omega

end Purelib.Polynomial.Winding.Box.Leading
