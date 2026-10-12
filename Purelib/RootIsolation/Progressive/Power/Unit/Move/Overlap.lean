module

import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
public import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Power.Unit.Move.Budget
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Budget

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

open Purelib.Data.Gaussian

/-- Construct the original same-box Rouché bridge from a source robust owner to the transported target owner. -/
def unitMoveBridge
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    OwnerBridge
      (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo).polynomial
      (Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).polynomial := by
  let owner := Owner.Local.Transport.castOwner
    (Progressive.Power.Unit.Frame.robustChamberFrame_polynomial (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo)
    ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree
      degreeAtLeastTwo).owner index)
  let raw := OwnerBridge.ofForward owner
    (Progressive.Power.Owner.Transport.ownerMoveRouche (target := target) degree owner (by
      dsimp only [owner]
      rw [Owner.Local.Transport.castOwner_clearance_bound,
        Progressive.Power.Unit.Frame.robustChamberFrame_owner_clearance_bound]
      exact small.owner _))
  exact raw.cast
    (Progressive.Power.Unit.Frame.robustChamberFrame_polynomial (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).symm
    (Progressive.Power.Unit.Move.Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree
      degreeAtLeastTwo small).symm
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

open Purelib.Data.Gaussian

/-- The unit-move bridge retains the exact indexed source robust box. -/
@[simp] theorem unitMoveBridge_box
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box =
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  rw [unitMoveBridge, OwnerBridge.cast_box]
  exact Owner.Local.Transport.castOwner_box _ _
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

open Purelib.Data.Gaussian

/-- Build the chamber overlap using the original finite index casts and same-box Rouché bridges. -/
def unitMoveOverlap
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo)
      (Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small) where
  matching := Data.Fin.Bijection.cast
    (Progressive.Power.Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo)
  bridge := unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small
  bridge_refines_left := by
    intro index
    rw [unitMoveBridge_box]
    exact Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [unitMoveBridge_box,
      Data.Fin.Bijection.cast_forward,
      Progressive.Power.Unit.Move.Frame.unitTransportedFrame_owner_box]
    exact Box.refines_refl _
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap

end
