module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Geometry.Polynomial.Path.Clearance.UnitCircle
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Winding.Edge.Product
import Purelib.RootIsolation.Power.Unit.Circuit.Clearance
public import Purelib.RootIsolation.Power.Unit.Circuit.Point
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Circuit.Product

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul normSq_zero)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Multiplication by the quarter rotation relates the coordinate edge to
its right-half-plane edge by the finite product formula. -/
theorem unitCircuitEdgeProductFormula
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) :
    Winding.Edge.Product.LineProductFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) 0 1 := open Purelib.Data in
          open Purelib.Geometry.Rational in by
  let source := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index
  let target := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)
  have sourceUnit : normSq source = 1 := by
    dsimp only [source, Power.Unit.Circuit.Point.unitCircuitPoint]
    rw [normSq_mul, Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier_unit,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_unit,
      Fraction.Field.one_mul]
  have targetUnit : normSq target = 1 := by
    dsimp only [target, Power.Unit.Circuit.Point.unitCircuitPoint]
    rw [normSq_mul, Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier_unit,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_unit,
      Fraction.Field.one_mul]
  have sourceNonzero : source ≠ 0 := Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit
  have targetNonzero : target ≠ 0 := Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit
  have rotationNonzero : Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter ≠ 0 := by
    intro zero
    have normZero := congrArg normSq zero
    rw [Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation_normSq, normSq_zero] at normZero
    exact (by decide : (2 : Fraction.Rational) ≠ 0) normZero
  apply Winding.Edge.Product.lineProductFormula_of_clearances
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
    source (target - source) (by decide)
    (Power.Unit.Circuit.Clearance.unitCircuitCoordinateEdgeCertificate quarter degree degreeAtLeastTwo
      indexBound)
    (Geometry.Polynomial.Path.Clearance.UnitCircle.unitCircuitRotationConstantCertificate quarter source (target -
      source))
  · simpa only [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
      Affine.Segment.line_segment_zero] using sourceNonzero
  · simpa only [Dense.Gaussian.Constants.gaussianConstant_eval] using rotationNonzero
  · simpa only [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
      Affine.Segment.line_segment_one] using targetNonzero
  · simpa only [Dense.Gaussian.Constants.gaussianConstant_eval] using rotationNonzero
end Purelib.RootIsolation.Power.Unit.Circuit.Product

end
