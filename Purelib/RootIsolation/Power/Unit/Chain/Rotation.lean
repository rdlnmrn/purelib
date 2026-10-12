module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Polynomial.Winding.Edge.Product
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Constant
import Purelib.Polynomial.Winding.Polygon.HalfPlane
public import Purelib.Polynomial.Winding.Polygon.Product
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Move.Budget
public import Purelib.RootIsolation.Winding.Polygon.UnitCircle.Rotation
public import Purelib.RootIsolation.Power.Unit.Chain.Vertices
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- The two finite edgewise formulas used to compare one subdivided unit
quarter with its fixed right-half-plane rotation. -/
structure RotationFormulas
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter) {start finish :
      UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish) : Prop where
  /-- The original edgewise right-half-plane formulas for the rotated retained parameter chain. -/ halfPlane :
    Winding.Polygon.HalfPlane.ChainHalfPlaneFormula
    (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter) start.value chain.vertices
  /-- The original edgewise product formulas for the coordinate polynomial and fixed quarter rotation. -/ product :
    Winding.Polygon.Product.ChainProductFormula
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
    start.value chain.vertices
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

namespace Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

open Purelib.Data.Gaussian
section UnitChain

/-- Transport the retained half-plane and product formulas along equality of the chain's finish vertex. -/
theorem castFinish
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter)
    {start left right : UnitVertex} (same : left = right)
    {chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start left}
    (formulas : Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter chain) :
    Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter (Power.Unit.Chain.Basic.UnitChain.castFinish same chain)
      := by
  subst right
  exact formulas
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

open Purelib.Data.Gaussian
section UnitChain

/-- Prepend the supplied edge formulas to the retained tail's half-plane and product formulas. -/
theorem cons
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter)
    {source middle finish : UnitVertex}
    {small : Power.Unit.Move.Budget.UnitMoveSmall source.unit middle.unit degree degreeAtLeastTwo}
    {remaining : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo middle finish}
    (edgeHalfPlane : Dense.Rational.CauchyIndex.HalfPlane.Formula
      (Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        source.value (middle.value - source.value))
      (Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        source.value (middle.value - source.value)) 0 1)
    (edgeProduct : Winding.Edge.Product.LineProductFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
      source.value (middle.value - source.value) 0 1)
    (tail : Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter remaining) :
    Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter (Power.Unit.Chain.Basic.UnitChain.cons small remaining) :=
  { halfPlane := .cons edgeHalfPlane tail.halfPlane
    product := .cons edgeProduct tail.product }
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

open Purelib.Data.Gaussian
section UnitChain

/-- The open raw winding of one rotated quarter chain is reduced entirely
to its two displayed endpoints. -/
theorem coordinateRaw_eq_endpoint
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {quarter : UnitCircuitQuarter} {start finish :
      UnitVertex}
    {chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish}
    (formulas : Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter chain) :
    Winding.Polygon.Basic.chainRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start.value chain.vertices =
      Power.Unit.Chain.Basic.UnitChain.rotationEndpointCorrection quarter start.value -
        Power.Unit.Chain.Basic.UnitChain.rotationEndpointCorrection quarter finish.value := by
  have halfPlane :=
    Winding.Polygon.HalfPlane.chainRaw_eq_endpoint_corrections_of_halfPlane
      (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter) start.value chain.vertices
        formulas.halfPlane
  rw [chain.vertices_terminal] at halfPlane
  have product := Winding.Polygon.Product.chainRaw_mul_of_formula
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    (Dense.Gaussian.Constants.gaussianConstant (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter))
    start.value chain.vertices formulas.product
  have constantZero := Winding.Polygon.Constant.chainRaw_gaussianConstant_zero
    (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation_ne_zero quarter) start.value chain.vertices
  unfold Power.Unit.Chain.Basic.UnitChain.rotationEndpointCorrection
  unfold Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate at halfPlane ⊢
  rw [halfPlane, constantZero] at product
  rw [chain.vertices_terminal] at product
  omega
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

open Purelib.Data.Gaussian
section UnitChain

/-- The empty retained chain has the original empty half-plane and product formulas. -/
theorem nil
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter) (vertex :
      UnitVertex) :
    Power.Unit.Chain.Basic.UnitChain.RotationFormulas (degree := degree)
      (degreeAtLeastTwo := degreeAtLeastTwo) quarter
      (Power.Unit.Chain.Basic.UnitChain.nil vertex) :=
  { halfPlane := Winding.Polygon.HalfPlane.ChainHalfPlaneFormula.nil vertex.value
    product := Winding.Polygon.Product.ChainProductFormula.nil vertex.value }
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Rotation.UnitChain.RotationFormulas

end
