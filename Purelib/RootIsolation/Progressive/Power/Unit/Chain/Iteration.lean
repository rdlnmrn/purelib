module

public import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Iteration
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
public import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Path
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- The final owner index after repeated closed chains equals iteration of the original monodromy permutation. -/
theorem repeatClosed_finalIndex
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index) :
    ∀ circuits : Nat,
      (chain.repeatClosed circuits).toPath.finalIndex index =
        Data.Fin.Bijection.iterateForward
          chain.toPath.monodromy circuits index
  | 0 => rfl
  | circuits + 1 => by
      rw [Power.Unit.Chain.Basic.UnitChain.repeatClosed, Power.Unit.Chain.Basic.UnitChain.toPath_append,
        Progressive.Chamber.Path.Basic.ChamberPath.finalIndex_append]
      rw [repeatClosed_finalIndex chain index circuits]
      rfl
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
