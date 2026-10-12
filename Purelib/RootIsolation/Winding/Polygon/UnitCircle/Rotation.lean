module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation
public import Purelib.Polynomial.Winding.Edge.Product
public import Purelib.Polynomial.Winding.Polygon.HalfPlane
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data

open Purelib

open Purelib.Polynomial

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Add the half-plane and constant-product vertex corrections for one quarter-circle rotation.

The integer correction uses the original quarter, its rotation multiplier and the displayed Gaussian endpoint. -/
def rotationEndpointCorrection
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (point : Gaussian.Basic.Canonical) : Int :=
  (Winding.Polygon.HalfPlane.vertexHalfPlaneCorrection2
      (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter) point : Int) +
    Winding.Edge.Product.vertexProductCorrection2
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
        point
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end

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

namespace Purelib.RootIsolation.Winding.Polygon.UnitCircle.Rotation

open Purelib.Data.Gaussian

open Purelib.RootIsolation in
/-- The endpoint rotation correction drops by exactly one across each displayed quarter-circle step. -/
theorem unitQuarter_rotationCorrection_difference
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) :
    Power.Unit.Chain.Basic.UnitChain.rotationEndpointCorrection quarter
        (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier quarter) -
      Power.Unit.Chain.Basic.UnitChain.rotationEndpointCorrection quarter
        (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier quarter * ⟨0, 1⟩) = 1 := by
  cases quarter <;> decide
end Purelib.RootIsolation.Winding.Polygon.UnitCircle.Rotation

end
