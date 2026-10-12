module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Circuit.Chain
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
public import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Path
import Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop

open Purelib.Data.Gaussian

/-- The concrete closed finite chamber path for the family `Z^d-w`. -/
def unitCircuitLoop (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Progressive.Chamber.Path.Basic.ChamberPath
      ((Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).frame degree
        degreeAtLeastTwo)
      ((Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).frame degree
        degreeAtLeastTwo) :=
  (Power.Unit.Circuit.Chain.unitCircuitChain degree degreeAtLeastTwo).toPath
end Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop

end
