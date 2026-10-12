module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
public import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Vertex

open Purelib.Data.Gaussian

/-- Package the indexed rational quarter-circuit point with its retained unit-quadrance proof. -/
def unitCircuitVertex (quarter :
  Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : Geometry.Gaussian.UnitCircle.Basic.UnitVertex where
  value := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index
  unit := Power.Unit.Circuit.Point.unitCircuitPoint_unit quarter degree degreeAtLeastTwo index
end Purelib.RootIsolation.Power.Unit.Circuit.Vertex

end
