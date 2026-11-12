module

public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
public import Purelib.RootIsolation.Owner.Local.Preparation
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Budget
import Purelib.RootIsolation.Owner.Family.Transport

/-! # Transported unit-power chamber owners consuming exact cached source owners -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Polynomial.Power.Gaussian.Progressive

/-- Transport an exact cached source owner to its original matched target occurrence.

The original unit move, degree and source index remain fixed. The same owner
transport and polynomial casts consume the cached box and boundary clearance.
The complete target-owner equality identifies the original transported frame.
-/
@[expose] def fromSource {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree degreeTwo).owner index)) :
    Owner.Local.Preparation.Prepared
      ((unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)) :=
  let originalPolynomial := Frame.robustChamberFrame_polynomial
    (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo
  let cached := Owner.Local.Transport.castOwner originalPolynomial prepared.owner
  have movedSmall : normSq (source - target) < cached.clearance.bound := by
    rewrite [Owner.Local.Transport.castOwner_clearance_bound, prepared.owner_eq,
      Frame.robustChamberFrame_owner_clearance_bound]
    exact small.owner (Fin.cast (Frame.robustChamberFrame_degree
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo) index)
  let moved := Owner.Transport.transportedOwner degree cached movedSmall
  let retained := Owner.Local.Transport.castOwner
    (Coefficients.coefficientTable_polynomial target degree).symm moved
  { owner := retained
    owner_eq := by
      rcases prepared with ⟨owner, same⟩
      cases same
      unfold Chamber.Frame.ChamberFrame.owner unitTransportedFrame
      rewrite [Owner.Family.Transport.castOwnerFamily_owner]
      rfl }

/-- The transported preparation retains the actual supplied cached source box.

Only the polynomial and boundary certificate change under the original move;
the source occurrence's exact retained rational box is reused.
-/
theorem fromSource_box {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree degreeTwo).owner index)) :
    (fromSource sourceUnit targetUnit degree degreeTwo small index prepared).owner.box =
      prepared.owner.box :=
  ((congrArg Owner.Local.Basic.LocalOwner.box
    (fromSource sourceUnit targetUnit degree degreeTwo small index prepared).owner_eq).trans
    (unitTransportedFrame_owner_box sourceUnit targetUnit degree degreeTwo small index)).trans
    (congrArg Owner.Local.Basic.LocalOwner.box prepared.owner_eq).symm

end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame.Preparation

end
