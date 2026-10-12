module

public import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Progressive.Chamber.Cycle.Divisibility
public import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop
import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Return
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Monodromy

open Purelib.Data.Gaussian

/-- Headline finite monodromy theorem for `Z^d-w`: the explicitly computed
rational unit circuit permutes the `d` isolated owner boxes in one cycle.
Every ingredient is a bounded rational calculation; in particular, the
returned-lift winding used to exclude a shorter orbit is constructed by the
finite sign-event scanner above. -/
theorem unitCircuitMonodromy_isSingleCycle
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Data.Fin.Bijection.IsSingleCycle
      (Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop degree degreeAtLeastTwo).monodromy := open Purelib.Data in by
  apply Progressive.Chamber.Cycle.Divisibility.monodromy_isSingleCycle_of_returnWinding degree
    (loop := Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop degree degreeAtLeastTwo)
  · unfold Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
    exact Progressive.Power.Unit.Frame.robustChamberFrame_degree
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
        (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).unit)
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).unit
      degree degreeAtLeastTwo
  · intro index circuits _circuitsPositive returned
    exact Progressive.Power.Unit.Circuit.Return.unitCircuitReturnWindingCertificate degree degreeAtLeastTwo
      index circuits returned
end Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Monodromy

end
