module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Circuit.Point
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Join

open Purelib.Data.Gaussian

/-- The four subdivided quarters join without a geometric gap and the last
quarter returns to the first vertex. -/
theorem unitCircuitQuarters_join (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Circuit.Point.unitCircuitPoint .first degree degreeAtLeastTwo
          (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) =
        Power.Unit.Circuit.Point.unitCircuitPoint .second degree degreeAtLeastTwo 0 ∧
      Power.Unit.Circuit.Point.unitCircuitPoint .second degree degreeAtLeastTwo
          (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) =
        Power.Unit.Circuit.Point.unitCircuitPoint .third degree degreeAtLeastTwo 0 ∧
      Power.Unit.Circuit.Point.unitCircuitPoint .third degree degreeAtLeastTwo
          (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) =
        Power.Unit.Circuit.Point.unitCircuitPoint .fourth degree degreeAtLeastTwo 0 ∧
      Power.Unit.Circuit.Point.unitCircuitPoint .fourth degree degreeAtLeastTwo
          (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) =
        Power.Unit.Circuit.Point.unitCircuitPoint .first degree degreeAtLeastTwo 0 := by
  simp only [Power.Unit.Circuit.Point.unitCircuitPoint, Power.Unit.Circuit.Subdivision.unitCircuitParameter_last,
    Power.Unit.Circuit.Subdivision.unitCircuitParameter_zero,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_one,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_zero,
    Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier]
  decide
end Purelib.RootIsolation.Power.Unit.Circuit.Join

end
