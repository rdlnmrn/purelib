module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Interval.Basic
import all Purelib.Geometry.Polynomial.Path.Clearance.Nonzero

import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.Polynomial.Winding.Edge.Product
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Segment.Clearance
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

open Purelib.Data.Rat.Interval (Bounds)

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Power.Unit.Segment.Product

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Product formula for two successive positive coordinate powers along one
robust lift segment. -/
theorem unitRobustSegmentProductFormula
    {parameter start finish : Gaussian.Basic.Canonical}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    (exponent : Nat) :
    Winding.Edge.Product.LineProductFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start (finish - start) 0 1 := by
  let left := Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside exponent
  let right := Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside 0
  apply Winding.Edge.Product.lineProductFormula_of_clearances
    (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start (finish - start)
    (by decide) left right
  · exact Geometry.Polynomial.Path.Clearance.Nonzero.path_value_ne_zero_of_certificate _ _ _ left
      (show ({ lower := 0, upper := 1, valid := by decide } :
        Bounds).Contains 0 from ⟨le_rfl, by decide⟩)
  · simpa only [show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Geometry.Polynomial.Path.Clearance.Nonzero.path_value_ne_zero_of_certificate
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0) start (finish - start)
        right
        (show ({ lower := 0, upper := 1, valid := by decide } :
          Bounds).Contains 0 from ⟨le_rfl, by decide⟩)
  · exact Geometry.Polynomial.Path.Clearance.Nonzero.path_value_ne_zero_of_certificate _ _ _ left
      (show ({ lower := 0, upper := 1, valid := by decide } :
        Bounds).Contains 1 from ⟨by decide, le_rfl⟩)
  · simpa only [show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Geometry.Polynomial.Path.Clearance.Nonzero.path_value_ne_zero_of_certificate
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0) start (finish - start)
        right
        (show ({ lower := 0, upper := 1, valid := by decide } :
          Bounds).Contains 1 from ⟨by decide, le_rfl⟩)
end Purelib.RootIsolation.Power.Unit.Segment.Product

end
