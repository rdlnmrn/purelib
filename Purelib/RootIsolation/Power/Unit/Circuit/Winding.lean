module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Rotation
import Purelib.RootIsolation.Power.Unit.Chain.Winding
public import Purelib.RootIsolation.Power.Unit.Circuit.Chain
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
public import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Lift
import Purelib.RootIsolation.Winding.Polygon.UnitCircle.Rotation
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Iteration
import Purelib.RootIsolation.Power.Unit.Chain.Vertices
import Purelib.Tactic.Ring

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power.Unit.Chain.Basic (UnitChain)

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Winding

open Purelib.Data.Gaussian

/-- Every explicitly subdivided stereographic quarter contributes one unit
of the repository's raw winding. -/
theorem unitQuarterChain_raw_eq_one
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Winding.Polygon.Basic.chainRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0).value
        (Power.Unit.Circuit.Chain.unitQuarterChain quarter degree degreeAtLeastTwo).vertices = 1 := by
  have identity :
      Winding.Polygon.Basic.chainRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0).value
          (Power.Unit.Circuit.Chain.unitQuarterChain quarter degree degreeAtLeastTwo).vertices =
        UnitChain.rotationEndpointCorrection quarter
            (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0).value -
          UnitChain.rotationEndpointCorrection quarter
            (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
              (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)).value :=
    Power.Unit.Chain.Rotation.UnitChain.RotationFormulas.coordinateRaw_eq_endpoint
      (Power.Unit.Circuit.Chain.unitQuarterChain_rotationFormulas quarter degree degreeAtLeastTwo)
  rw [Power.Unit.Circuit.Chain.unitCircuitVertex_zero_value,
    Power.Unit.Circuit.Chain.unitCircuitVertex_last_value] at identity
  rw [Winding.Polygon.UnitCircle.Rotation.unitQuarter_rotationCorrection_difference] at identity
  rw [Power.Unit.Circuit.Chain.unitCircuitVertex_zero_value]
  rw [identity]
end Purelib.RootIsolation.Power.Unit.Circuit.Winding

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Winding

open Purelib.Data.Gaussian

/-- The retained quarter chain has raw parameter winding exactly one. -/
theorem unitQuarterChain_parameterRaw_eq_one
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain.parameterRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Power.Unit.Circuit.Chain.unitQuarterChain quarter degree degreeAtLeastTwo) = 1 :=
  unitQuarterChain_raw_eq_one quarter degree degreeAtLeastTwo
end Purelib.RootIsolation.Power.Unit.Circuit.Winding

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Winding

open Purelib.Data.Gaussian

/-- The four retained quarter chains and equal-value connectors have total raw parameter winding exactly four. -/
theorem unitCircuitChain_parameterRaw_eq_four
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain.parameterRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Power.Unit.Circuit.Chain.unitCircuitChain degree degreeAtLeastTwo) = 4 := by
  unfold Power.Unit.Circuit.Chain.unitCircuitChain
  simp only [UnitChain.parameterRaw_append,
    unitQuarterChain_parameterRaw_eq_one,
    Power.Unit.Circuit.Chain.unitCircuitFirstSecondJoin, Power.Unit.Circuit.Chain.unitCircuitSecondThirdJoin,
    Power.Unit.Circuit.Chain.unitCircuitThirdFourthJoin, Power.Unit.Circuit.Chain.unitCircuitFourthFirstJoin,
    UnitChain.parameterRaw_equalValue]
  decide
end Purelib.RootIsolation.Power.Unit.Circuit.Winding

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Winding

open Purelib.Data.Gaussian

/-- Repeating the explicit unit circuit gives the corresponding exact raw
winding on the synchronized parameter polygon, including its stationary
connector copies. -/
theorem repeatedUnitCircuitParameterPolygon_windingFour
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (circuits : Nat) :
    Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).value
        (UnitChain.liftParameterVertices
          ((Power.Unit.Circuit.Chain.unitCircuitChain degree degreeAtLeastTwo).repeatClosed circuits)) =
      (4 : Int) * circuits := by
  rw [UnitChain.closedLiftParameterRaw_eq_parameterRaw,
    UnitChain.parameterRaw_repeatClosed,
    unitCircuitChain_parameterRaw_eq_four]
  ring1
end Purelib.RootIsolation.Power.Unit.Circuit.Winding

end
