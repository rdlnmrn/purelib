module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Basic

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

/-- Concatenate the original closed unit-move chain the supplied finite number of times. -/
def repeatClosed
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex) : Nat →
      Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex
  | 0 => .nil vertex
  | circuits + 1 => (repeatClosed chain circuits).append chain
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
