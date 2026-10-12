module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Evaluation

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

namespace Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Multiply the coordinate polynomial by the exact quarter-circuit rotation scalar. -/
def unitCircuitRotatedCoordinate
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) : (Dense.Basic.DensePolynomial
      Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial *
    Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter)
end Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation

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

namespace Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The rotated coordinate evaluates to the quarter-circuit scalar times the point. -/
@[simp] theorem unitCircuitRotatedCoordinate_eval
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (point : Gaussian.Basic.Canonical) :
    (unitCircuitRotatedCoordinate quarter).eval point =
      Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * point := by
  rw [unitCircuitRotatedCoordinate,
    Dense.Basic.DensePolynomial.eval_mul,
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
    Dense.Gaussian.Constants.gaussianConstant_eval,
    Gaussian.Basic.mul_comm]
end Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation

end
