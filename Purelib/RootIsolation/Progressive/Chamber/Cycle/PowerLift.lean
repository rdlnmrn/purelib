module
import Purelib.Data.Nat.Subtraction

public import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Progressive.Chamber.Cycle.Divisibility
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Winding.Polygon.Power.ReturnedLift
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport

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

namespace Purelib.RootIsolation.Progressive.Chamber.Cycle.PowerLift

open Purelib.Data.Gaussian

open Purelib.Data.Nat

/-- Geometric form of the single-cycle result.  Its premise contains only
the returned finite rational polygons and the per-edge executable product
and Rouché certificates; divisibility is no longer an assumed arithmetic
fact. -/
theorem monodromy_isSingleCycle_of_returnedLifts
    {frame : Progressive.Chamber.Frame.ChamberFrame}
    (degree : Data.Nat.Positive.RootDegree)
    (degreeEq : frame.degree = degree.value)
    (loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame)
    (returnedLift : ∀ (index : frame.Index) (circuits : Nat),
      0 < circuits →
      Data.Fin.Bijection.iterateForward
          loop.monodromy circuits index = index →
        RootIsolation.Winding.Polygon.Power.ReturnedLift degree (circuits - 1)) :
    Data.Fin.Bijection.IsSingleCycle loop.monodromy := by
  apply Progressive.Chamber.Cycle.Divisibility.monodromy_isSingleCycle_of_returnWinding degree degreeEq loop
  intro index circuits circuitsPositive returned
  have certificate :=
    (returnedLift index circuits circuitsPositive returned)
      |>.returnWindingCertificate
  have predecessor : circuits - 1 + 1 = circuits :=
    Subtraction.sub_add_cancel circuitsPositive
  simpa only [predecessor] using certificate

end Purelib.RootIsolation.Progressive.Chamber.Cycle.PowerLift

end
