module

public import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation
import Purelib.RootIsolation.Owner.Local.Preparation

/-! # Prepared local owners at their original robust chamber occurrences -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Preparation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation

/-- Attach an exact saved robust owner to its original chamber-frame index.

The original degree equality supplies the bounded power-family index. Cached
box and clearance readings are transported through the existing frame laws;
the resulting complete owner still belongs to that same original frame. -/
@[expose] def fromOwner {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame nonzero unit degree degreeTwo).Index)
    (prepared : Unit.Owner.Preparation.Prepared nonzero unit degree degreeTwo
      (Fin.cast (robustChamberFrame_degree nonzero unit degree degreeTwo) index)) :
    Owner.Local.Preparation.Prepared ((robustChamberFrame nonzero unit degree degreeTwo).owner index) :=
  Owner.Local.Preparation.fromReadback _ prepared.owner.owner.box prepared.owner.owner.clearance.bound
    ((congrArg Owner.Local.Basic.LocalOwner.box prepared.owner.owner_eq).trans
      (robustChamberFrame_owner_box nonzero unit degree degreeTwo index).symm)
    ((congrArg (fun owner => owner.clearance.bound) prepared.owner.owner_eq).trans
      (robustChamberFrame_owner_clearance_bound nonzero unit degree degreeTwo index).symm)

end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Preparation
