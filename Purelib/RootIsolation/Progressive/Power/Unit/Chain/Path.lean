module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path
public import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Power.Unit.Frame

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

/-- Forget the unit-vertex packaging and execute every certified edge as the
three finite chamber overlaps supplied by `unitSmallMovePath`. -/
def toPath {degree : Data.Nat.Positive.RootDegree}
  {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} →
      Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish →
      Progressive.Chamber.Path.Basic.ChamberPath
        (start.frame degree degreeAtLeastTwo)
        (finish.frame degree degreeAtLeastTwo)
  | _, _, .nil vertex => .nil (vertex.frame degree degreeAtLeastTwo)
  | _, _, .cons small remaining =>
      (Progressive.Power.Unit.Move.Path.unitSmallMovePath _ _ degree degreeAtLeastTwo small).append
        remaining.toPath
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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Converting concatenated unit chains to chamber paths preserves their original path concatenation. -/
theorem toPath_append
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (first : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start middle)
    (second : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo middle finish) :
    (first.append second).toPath = first.toPath.append second.toPath := by
  induction first with
  | nil => rfl
  | cons small remaining inductionHypothesis =>
      simp only [Power.Unit.Chain.Basic.UnitChain.append, toPath, inductionHypothesis]
      exact (Progressive.Chamber.Path.Basic.ChamberPath.append_assoc
        (Progressive.Power.Unit.Move.Path.unitSmallMovePath _ _ degree degreeAtLeastTwo small)
        remaining.toPath second.toPath).symm
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
