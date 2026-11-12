module

public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Track
public import Purelib.RootIsolation.Owner.Local.Preparation
public import Purelib.RootIsolation.Owner.Family.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Owner
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Bounds
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.Geometry.Rational.Box.Refinement

/-! # Original transported unit-power tracks from retained source owners and bands -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Polynomial
open Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Power.Gaussian.Progressive
open Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)

/-- The original transported power family's raw state in its retained global square. -/
abbrev Raw (target : Canonical) (degree : RootDegree) :=
  State.Raw.RawWindingState (Power.Gaussian.rootPolynomial target degree)
    (largeSquareBox (Power.Gaussian.rootPolynomial target degree))

/-- The original transported winding-one state in the same retained global square. -/
abbrev State (target : Canonical) (degree : RootDegree) :=
  RootIsolation.State.WindingOne.Basic.WindingOneState (Power.Gaussian.rootPolynomial target degree)
    (largeSquareBox (Power.Gaussian.rootPolynomial target degree))

/-- Transport a retained exact original robust source owner into the original target raw state.

The supplied occurrence and unit move remain unchanged. Its actual source box,
properness and boundary certificate are consumed by the original coefficient
transport; the full raw-state equality preserves its original ambient and winding.
-/
@[expose] def rawFromOwner {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo) (index : Fin degree.value)
    (prepared : Owner.Local.Preparation.Prepared
      (Unit.Owner.unitRobustOwner (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo index)) :
    { value : Raw target degree // value =
      unitTransportedRawState sourceUnit targetUnit degree degreeTwo small index } :=
  let sourceOwner := prepared.owner
  let targetOwner := Owner.Transport.transportedOwner (target := target) degree sourceOwner (by
    change normSq (source - target) < prepared.owner.clearance.bound
    rewrite [prepared.owner_eq]
    exact small.owner index)
  let retained : Raw target degree :=
    { box := sourceOwner.box
      refinesAmbient := by
        change prepared.owner.box.Refines _
        rewrite [prepared.owner_eq, ← Power.Bounds.largeSquareBox_polynomial_eq_of_normSq_eq
          (sourceUnit.trans targetUnit.symm) degree]
        exact Power.Unit.Box.unitRobustBox_refinesAmbient (nonzero_of_normSq_eq_one sourceUnit)
          sourceUnit degree degreeTwo index
      proper := targetOwner.proper
      clearance := targetOwner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := targetOwner.rawWindingFour.symm.trans zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
  ⟨retained, by
    rcases prepared with ⟨owner, same⟩
    cases same
    rfl⟩

/-- Recover the original power-polynomial owner from its exact transported frame occurrence.

The supplied complete owner is cast along the original coefficient-table
identity. Its original occurrence, box, clearance and winding record remain
unchanged; the equality identifies the same original coefficient transport.
-/
@[expose] def ownerFromFrame {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index)) :
    Owner.Local.Preparation.Prepared
      (Owner.Transport.transportedOwner degree
        (Unit.Owner.unitRobustOwner (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo
          (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))
        (small.owner (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))) :=
  { owner := Owner.Local.Transport.castOwner
      (Coefficients.coefficientTable_polynomial target degree) prepared.owner
    owner_eq := by
      rewrite [prepared.owner_eq]
      unfold Chamber.Frame.ChamberFrame.owner Frame.unitTransportedFrame
      rewrite [Owner.Family.Transport.castOwnerFamily_owner, Owner.Local.Transport.castOwner_inverse]
      apply Owner.Transport.transportedOwner_congr
      dsimp only [Unit.Frame.robustChamberFrame, Chamber.Frame.ChamberFrame.owner]
      rewrite [Owner.Family.Transport.castOwnerFamilyFull_owner_target]
      change Owner.Local.Transport.castOwner
        (Coefficients.coefficientTable_polynomial source degree)
        (Owner.Local.Transport.castOwner
          (Coefficients.coefficientTable_polynomial source degree).symm
          (Unit.Owner.unitRobustOwner (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo
            (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))) = _
      exact Owner.Local.Transport.castOwner_inverse
        (Coefficients.coefficientTable_polynomial source degree).symm _ }

/-- Read the original transported raw state from its actual retained transported frame owner.

The original coefficient transport is reused rather than reconstructed. Only
its retained box and boundary certificate execute; its full owner equality
supplies the unchanged source occurrence and ambient-refinement evidence.
-/
@[expose] def rawFromFrame {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index)) :
    { value : Raw target degree // value = unitTransportedRawState
      sourceUnit targetUnit degree degreeTwo small
      (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) } :=
  let retained := ownerFromFrame sourceUnit targetUnit degree degreeTwo small index prepared
  let raw : Raw target degree :=
    { box := retained.owner.box
      refinesAmbient := by
        rewrite [retained.owner_eq]
        change (Power.Unit.Box.unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
          sourceUnit degree degreeTwo
          (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).Refines _
        rewrite [← Power.Bounds.largeSquareBox_polynomial_eq_of_normSq_eq
          (sourceUnit.trans targetUnit.symm) degree]
        exact Power.Unit.Box.unitRobustBox_refinesAmbient (nonzero_of_normSq_eq_one sourceUnit)
          sourceUnit degree degreeTwo _
      proper := retained.owner.proper
      clearance := retained.owner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := retained.owner.rawWindingFour.symm.trans zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
  ⟨raw, by
    apply RootIsolation.State.Raw.RawWindingState.eq_of_box_bound
    · exact congrArg Owner.Local.Basic.LocalOwner.box retained.owner_eq
    · exact congrArg (fun owner => owner.clearance.bound) retained.owner_eq⟩

/-- The original transported raw state has the same box as its indexed frame owner.

The full cached-owner readback supplies this equality. No tolerance-one band
or numerical refinement is part of this owner identification.
-/
theorem raw_box {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :
    (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
      (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).box =
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index).box := by
  let prepared : Owner.Local.Preparation.Prepared
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index) := ⟨_, rfl⟩
  let cached := rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared
  have boxEq : cached.val.box = prepared.owner.box := Owner.Local.Transport.castOwner_box _ _
  exact (congrArg (fun current => current.box) cached.property).symm.trans boxEq

/-- The original transported raw owner retains quadrupled winding four.

This is the coefficient-transported local owner's original winding
certificate, read before any extraction or assignment-radius computation.
-/
theorem raw_windingFour {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :
    Winding.Box.Basic.quadrupledBoxWinding (Power.Gaussian.rootPolynomial target degree)
      (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).box = 4 := by
  let prepared : Owner.Local.Preparation.Prepared
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index) := ⟨_, rfl⟩
  let cached := rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared
  rewrite [← cached.property]
  exact (ownerFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).owner.rawWindingFour

/-- The original transported raw owner is supported in the retained target partition's global square. -/
theorem raw_supported {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :
    (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
      (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).box.Refines
      (Power.Isolation.isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeTwo).boxes.isolation.support := by
  change (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
    (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).box.Refines
      (largeSquareBox (Power.Gaussian.rootPolynomial target degree))
  exact (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
    (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).refinesAmbient

/-- The canonical transported track starts inside that same original transported raw owner. -/
theorem track_initial_refines_raw {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index).initial.box.Refines
      (unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)).box := by
  rewrite [raw_box sourceUnit targetUnit degree degreeTwo small index]
  exact unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree degreeTwo small index

section

variable {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (prepared : Owner.Local.Preparation.Prepared
      ((Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index))

/-- The cached transported raw state reads the actual supplied frame owner's box. -/
theorem rawFromFrame_box :
    (rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).val.box = prepared.owner.box :=
  Owner.Local.Transport.castOwner_box _ _

/-- The cached transported raw state reads the actual supplied frame owner's boundary bound. -/
theorem rawFromFrame_bound :
    (rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).val.clearance.bound =
      prepared.owner.clearance.bound :=
  Owner.Local.Transport.castOwner_clearance_bound _ _

end

/-- Read the complete original transported winding-one state from its retained original band.

The band uses the exact cached transported raw state and the original fixed
accuracy one. Complete raw-state and band readbacks retain the original
source occurrence, four ambient lines, boundary certificate and winding.
-/
@[expose] def stateFromBand {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo) (index : Fin degree.value)
    (raw : { value : Raw target degree // value =
      unitTransportedRawState sourceUnit targetUnit degree degreeTwo small index })
    (band : Newton.Band.Basic.Output
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).squarefree raw.val 1)
    (same : band = Newton.Band.Build.extract
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).degreeAtLeastTwo
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).squarefree
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).elimination
      raw.val (by decide : (0 : Data.Rat.Fraction.Rational) < 1)) :
    { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small index } :=
  let retained : State target degree :=
    { box := band.box
      refinesAmbient := band.refinesAmbient
      proper := band.proper
      clearance := band.clearance
      rawWindingFour := band.rawWindingFour
      ambientLeftClearance := band.ambientLeftClearance
      ambientRightClearance := band.ambientRightClearance
      ambientBottomClearance := band.ambientBottomClearance
      ambientTopClearance := band.ambientTopClearance }
  ⟨retained, by
    rcases raw with ⟨raw, rawEq⟩
    cases rawEq
    cases same
    rfl⟩

/-- Read the original transported state from a band paid with the same cached input and elimination.

The complete original input and elimination equalities transport only the
band's certificate indices. Its actual source, Newton data, box and clearances
remain the paid cached output, with complete original-state readback.
-/
@[expose] def stateFromCachedBand {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo) (index : Fin degree.value)
    (input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial target degree))
    (inputEq : input = Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (Power.Gaussian.rootPolynomial target degree) input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (raw : { value : Raw target degree // value =
      unitTransportedRawState sourceUnit targetUnit degree degreeTwo small index })
    (band : Newton.Band.Basic.Output input.squarefree raw.val 1)
    (same : band = Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination raw.val
      (by decide : (0 : Data.Rat.Fraction.Rational) < 1)) :
    { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small index } :=
  stateFromBand sourceUnit targetUnit degree degreeTwo small index raw
    (Newton.Band.Basic.Output.castSquarefree (congrArg FTA.Squarefree.Input.squarefree inputEq) band)
    (by
      cases inputEq
      cases eliminationEq
      exact same)

/-- Initialize the original transported track from its exact retained winding-one state. -/
@[expose] def trackFromState {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo) (index : Fin degree.value)
    (state : { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small index }) :
    { value : RootIsolation.Track.Basic.WindingOneTrack (Power.Gaussian.rootPolynomial target degree)
      (largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = unitTransportedIsolatedTrack sourceUnit targetUnit degree degreeTwo small index } :=
  let input := Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo
  ⟨RootIsolation.Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree input.elimination state.val, by
    rcases state with ⟨state, same⟩
    cases same
    rfl⟩

/-- Attach the cached transported state to the original intermediate frame occurrence. -/
@[expose] def frameTrackFromState {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (state : { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small
        (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) }) :
    { value : RootIsolation.Track.Basic.WindingOneTrack (Power.Gaussian.rootPolynomial target degree)
      (largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index } :=
  trackFromState sourceUnit targetUnit degree degreeTwo small
    (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) state

/-- Attach the original transported state using the same retained input and elimination cache.

The supplied complete readbacks identify the original frame occurrence. The
new track closes over the actual elimination certificate and exact paid state;
no canonical input or elimination producer is executed to rebuild its data.
-/
@[expose] def frameTrackFromCachedState {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial target degree))
    (inputEq : input = Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (Power.Gaussian.rootPolynomial target degree) input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (state : { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small
        (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) }) :
    { value : RootIsolation.Track.Basic.WindingOneTrack (Power.Gaussian.rootPolynomial target degree)
      (largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index } :=
  ⟨RootIsolation.Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination state.val, by
    cases inputEq
    cases eliminationEq
    exact (frameTrackFromState sourceUnit targetUnit degree degreeTwo small index state).property⟩

/-- Supplied input and elimination caches preserve the complete original transported frame track. -/
theorem frameTrackFromCachedState_eq {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial target degree))
    (inputEq : input = Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (Power.Gaussian.rootPolynomial target degree) input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (state : { value : State target degree // value =
      unitTransportedIsolatedState sourceUnit targetUnit degree degreeTwo small
        (unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) }) :
    (frameTrackFromCachedState sourceUnit targetUnit degree degreeTwo small index
      input inputEq elimination eliminationEq state).val =
      (frameTrackFromState sourceUnit targetUnit degree degreeTwo small index state).val :=
  (frameTrackFromCachedState sourceUnit targetUnit degree degreeTwo small index
    input inputEq elimination eliminationEq state).property.trans
    (frameTrackFromState sourceUnit targetUnit degree degreeTwo small index state).property.symm

/-- Every exact cached transported frame track uses its original canonical Newton refinement. -/
theorem refine_eq {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (cachedTrack : { value : RootIsolation.Track.Basic.WindingOneTrack
      (Power.Gaussian.rootPolynomial target degree)
      (largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index })
    (current : State target degree) (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    cachedTrack.val.refine current epsilon positive = RootIsolation.Track.Newton.Refinement.refineState
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).degreeAtLeastTwo
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).squarefree
      (Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).elimination
      current epsilon positive := by
  rcases cachedTrack with ⟨track, same⟩
  cases same
  rfl

end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track.Preparation

end
