module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Riemann.Topology.PreparedStokes
import Init.Prelude
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Riemann.Topology

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedStokes

/-! ## Finite zero laws used by Gauss--Manin reduction -/

/-- Every displayed cellular boundary, containing both orientations of every lifted edge, contributes operational zero.
-/
def cellularBoundary_operational_zero {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (pairs : PreparedStokes.CellularEdgePairs curve) :
    Gaussian.Equivalence.NamedEquivalent pairs.boundarySum.name
      (Coherence.exact 0).name :=
  pairs.boundarySum_zero
end Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedStokes

end
