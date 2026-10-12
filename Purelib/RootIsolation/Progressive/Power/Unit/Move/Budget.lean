module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Clearance
public import Purelib.RootIsolation.Power.Unit.Move.Budget
public import Purelib.RootIsolation.Progressive.Power.Unit.Owner
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Data

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

namespace Purelib.RootIsolation.Power.Unit.Move.Budget.UnitMoveSmall

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- The common unit-move budget satisfies the boundary-clearance requirement of every retained robust owner. -/
theorem owner
    {source target : Gaussian.Basic.Canonical}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    normSq (source - target) <
      (Progressive.Power.Unit.Owner.unitRobustOwner (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree
        degreeAtLeastTwo index).clearance.bound := by
  change normSq (source - target) <
    (Power.Unit.Clearance.unitRobustBoundaryClearance (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).bound
  rw [Power.Unit.Clearance.unitRobustBoundaryClearance_uniform]
  exact small.distance
end Purelib.RootIsolation.Power.Unit.Move.Budget.UnitMoveSmall

end
