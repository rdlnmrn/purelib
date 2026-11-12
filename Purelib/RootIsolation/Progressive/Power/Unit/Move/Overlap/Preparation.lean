module

public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap
public import Purelib.RootIsolation.Owner.Local.Preparation
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Progressive.Power.Owner.Transport

/-! # Original unit-move bridges consuming retained complete source owners -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap.Preparation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

variable {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree degreeTwo).owner index))

/-- Build the original forward bridge from its actual cached source owner.

The same coefficient move and clearance comparison consume the supplied box
and bound. The complete bridge readback preserves both original endpoint
polynomials and the original selected occurrence.
-/
def fromSource : { value : OwnerBridge
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo).polynomial
      (Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial //
    value = unitMoveBridge sourceUnit targetUnit degree degreeTwo small index } :=
  let same := Frame.robustChamberFrame_polynomial (nonzero_of_normSq_eq_one sourceUnit)
    sourceUnit degree degreeTwo
  let owner := Owner.Local.Transport.castOwner same prepared.owner
  have bound : normSq (source - target) < owner.clearance.bound := by
    rewrite [Owner.Local.Transport.castOwner_clearance_bound, prepared.owner_eq,
      Frame.robustChamberFrame_owner_clearance_bound]
    exact small.owner _
  let bridge := (OwnerBridge.ofForward owner
    (Owner.Transport.ownerMoveRouche (target := target) degree owner bound)).cast same.symm
    (Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree degreeTwo small).symm
  ⟨bridge, by
    rcases prepared with ⟨owner, same⟩
    cases same
    rfl⟩

/-- The first bridge reuses the exact supplied cached source box. -/
theorem fromSource_box :
    (fromSource sourceUnit targetUnit degree degreeTwo small index prepared).val.box = prepared.owner.box := by
  unfold fromSource
  rewrite [OwnerBridge.cast_box]
  exact Owner.Local.Transport.castOwner_box _ _

/-- The first bridge reuses the exact supplied cached source clearance bound. -/
theorem fromSource_leftBound :
    (fromSource sourceUnit targetUnit degree degreeTwo small index prepared).val.leftClearance.bound =
      prepared.owner.clearance.bound := by
  unfold fromSource
  rewrite [OwnerBridge.cast_leftClearance_bound]
  exact Owner.Local.Transport.castOwner_clearance_bound _ _

end Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap.Preparation

end
