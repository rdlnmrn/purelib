module
import Purelib.RootIsolation.Refinement.Basic
public import Purelib.RootIsolation.Refinement.Source

public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching
public import Purelib.RootIsolation.Progressive.Power.Frame.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Track.Preparation
public import Purelib.RootIsolation.Exact.Ownership.Replay
import Purelib.RootIsolation.Power.Isolation
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients

/-! # Original transported-to-target owner matching from retained partition and track caches -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Polynomial
open Purelib.Polynomial.Power.Gaussian.Progressive

/-- Restore the complete original transported owner selection from actual retained caches.

The target partition includes its original track and remainder cells. The
transported source track and its actual assignment-radius refinement are
retained independently; their readbacks identify the original deterministic
selection and preserve its source and target occurrences.
-/
@[expose] def fromCaches {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (cachedTrack : { value : RootIsolation.Track.Basic.WindingOneTrack
      (Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index })
    (refined : Exact.Ownership.Replay.Refined targetFrame.isolation cachedTrack.val) :
    Exact.Ownership.Basic.OwnerSelection
      (Power.Isolation.isolationResult (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).boxes.isolation
      (Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index) :=
  let input := Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo
  Exact.Ownership.Replay.fromReadbacks input.degreeAtLeastTwo input.squarefree input.elimination _ _
    (Move.Track.unitTransportedFrameTrack_supported sourceUnit targetUnit degree degreeTwo small index)
    targetFrame.isolation targetFrame.isolation_eq cachedTrack.val cachedTrack.property refined

/-- Restored partition, track and refinement caches give the complete original owner selection. -/
theorem fromCaches_eq {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (cachedTrack : { value : RootIsolation.Track.Basic.WindingOneTrack
      (Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index })
    (refined : Exact.Ownership.Replay.Refined targetFrame.isolation cachedTrack.val) :
    fromCaches sourceUnit targetUnit degree degreeTwo small index targetFrame cachedTrack refined =
      unitTransportedOwnerSelection sourceUnit targetUnit degree degreeTwo small index :=
  Exact.Ownership.Replay.fromReadbacks_eq _ _ _ _ _ _ _ _ _ _ _

/-- A retained complete selection with its original deterministic assignment readback. -/
abbrev Selection {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :=
  { value : Exact.Ownership.Basic.OwnerSelection
      (Power.Isolation.isolationResult (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).boxes.isolation
      (Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index) //
    value = unitTransportedOwnerSelection sourceUnit targetUnit degree degreeTwo small index }

/-- Read the selected occurrence directly from the actual retained complete matching. -/
@[expose] def selected {source target : Canonical}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value}
    {small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo}
    {index : Fin (Coefficients.coefficientTable target degree).degree}
    (selection : Selection sourceUnit targetUnit degree degreeTwo small index) :
    Fin (Coefficients.coefficientTable target degree).degree :=
  Fin.cast (unitTargetTrackCountEq targetUnit degree degreeTwo) selection.val.owner

/-- The actual retained occurrence is the original finite owner-assignment map. -/
theorem selected_eq {source target : Canonical}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value}
    {small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo}
    {index : Fin (Coefficients.coefficientTable target degree).degree}
    (selection : Selection sourceUnit targetUnit degree degreeTwo small index) :
    selected selection = unitRebaseMap sourceUnit targetUnit degree degreeTwo small index :=
  congrArg (fun selected => Fin.cast (unitTargetTrackCountEq targetUnit degree degreeTwo)
    (Exact.Ownership.Basic.OwnerSelection.owner selected)) selection.property

/-- An actual certified assignment of the original transported raw owner and target partition.

The source is the original transported owner before tolerance-one extraction.
Its actual supplied refinement is retained without a canonical-state equality.
-/
abbrev Assignment {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :=
  Exact.Ownership.Basic.Assignment
    (Power.Isolation.isolationResult (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).boxes.isolation
    (Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
      (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))

/-- Assign an actual refinement of the original transported raw owner to the retained target partition.

The original raw box and occurrence remain the source. The supplied state
already pays the exact partition assignment radius; no intermediate
canonical track or tolerance-one extraction is evaluated.
-/
@[expose] def fromRawRefinement {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (refinement : RootIsolation.Refinement
      (Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))
      (Exact.Ownership.Radius.assignmentRadius _ _ targetFrame.isolation)) :
    Assignment sourceUnit targetUnit degree degreeTwo small index :=
  let input := targetFrame.input
  Exact.Ownership.Prepare.fromRawReadbacks input.degreeAtLeastTwo input.squarefree targetFrame.elimination _ _
    (Move.Track.Preparation.raw_supported sourceUnit targetUnit degree degreeTwo small index)
    targetFrame.isolation targetFrame.isolation_eq _ rfl refinement

/-- Assign a supplied refinement using complete retained raw-owner and target-partition readbacks.

The cached source can be the exact value returned by `rawFromFrame`. Both
complete equalities transport the original owners, while the actual successful
state and its numerical bound are consumed without recomputation.
-/
@[expose] def fromRawReadbacks {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (cachedRaw : { value : Move.Track.Preparation.Raw target degree //
      value = Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) })
    (refinement : RootIsolation.Refinement cachedRaw.val
      (Exact.Ownership.Radius.assignmentRadius _ _ targetFrame.isolation)) :
    Assignment sourceUnit targetUnit degree degreeTwo small index :=
  let input := targetFrame.input
  Exact.Ownership.Prepare.fromRawReadbacks input.degreeAtLeastTwo input.squarefree targetFrame.elimination _ _
    (Move.Track.Preparation.raw_supported sourceUnit targetUnit degree degreeTwo small index)
    targetFrame.isolation targetFrame.isolation_eq cachedRaw.val cachedRaw.property refinement

/-- Raw-owner assignment retains the complete supplied winding-one state. -/
theorem fromRawRefinement_state {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (refinement : RootIsolation.Refinement
      (Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index))
      (Exact.Ownership.Radius.assignmentRadius _ _ targetFrame.isolation)) :
    (fromRawRefinement sourceUnit targetUnit degree degreeTwo small index targetFrame refinement).refinement.state =
      refinement.state := by
  rcases targetFrame with ⟨frame, frameEq, isolation, isolationEq, input, inputEq, elimination, eliminationEq⟩
  cases isolationEq
  rfl

/-- Complete raw-source and partition readbacks retain the actual supplied numerical state. -/
theorem fromRawReadbacks_state {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (cachedRaw : { value : Move.Track.Preparation.Raw target degree //
      value = Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) })
    (refinement : RootIsolation.Refinement cachedRaw.val
      (Exact.Ownership.Radius.assignmentRadius _ _ targetFrame.isolation)) :
    (fromRawReadbacks sourceUnit targetUnit degree degreeTwo small index targetFrame
      cachedRaw refinement).refinement.state =
      refinement.state := by
  rcases targetFrame with ⟨frame, frameEq, isolation, isolationEq, input, inputEq, elimination, eliminationEq⟩
  rcases cachedRaw with ⟨raw, rawEq⟩
  cases isolationEq
  cases rawEq
  rfl

/-- Assign the original transported occurrence using its actual certified refinement and retained target partition.

The locator consumes the supplied state, original assignment radius and full
partition cache. Owner agreement is derived internally from finite winding
counts, not accepted as an input relation or canonical-state equality.
-/
@[expose] def fromRefinement {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (cachedTrack : { value : RootIsolation.Track.Basic.WindingOneTrack
      (Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial target degree)) //
      value = Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeTwo small index })
    (refinement : RootIsolation.Refinement cachedTrack.val.initial.raw
      (Exact.Ownership.Radius.assignmentRadius _ _ targetFrame.isolation)) :
    Assignment sourceUnit targetUnit degree degreeTwo small index :=
  let raw := Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
    (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)
  have contained : cachedTrack.val.initial.box.Refines raw.box := by
    rewrite [cachedTrack.property]
    exact Move.Track.Preparation.track_initial_refines_raw sourceUnit targetUnit degree degreeTwo small index
  fromRawRefinement sourceUnit targetUnit degree degreeTwo small index targetFrame
    (refinement.withSource raw contained)

namespace Assignment

/-- Read the original bounded target occurrence from the actual assignment. -/
@[expose] def selected {source target : Canonical}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value}
    {small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo}
    {index : Fin (Coefficients.coefficientTable target degree).degree}
    (assignment : Assignment sourceUnit targetUnit degree degreeTwo small index) :
    Fin (Coefficients.coefficientTable target degree).degree :=
  Fin.cast (unitTargetTrackCountEq targetUnit degree degreeTwo) assignment.owner

/-- The actual selected occurrence equals the original finite owner-assignment map.

The actual and canonical refinements are both strictly inside the same
original transported winding-four owner. Their finite count comparison
identifies only the owner index, retaining the actual supplied state.
-/
theorem selected_eq {source target : Canonical}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value}
    {small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo}
    {index : Fin (Coefficients.coefficientTable target degree).degree}
    (assignment : Assignment sourceUnit targetUnit degree degreeTwo small index) :
    selected assignment = unitRebaseMap sourceUnit targetUnit degree degreeTwo small index := by
  let input := Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo
  let raw := Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
    (Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index)
  let canonical := (unitTransportedOwnerSelection sourceUnit targetUnit degree degreeTwo small index).toAssignment
  let retained : Exact.Ownership.Basic.Assignment _ raw :=
    { refinement := canonical.refinement.withSource raw
        (Move.Track.Preparation.track_initial_refines_raw sourceUnit targetUnit degree degreeTwo small index)
      owner := canonical.owner
      strict := canonical.strict }
  have same := Exact.Ownership.Prepare.same_owner input.degreeAtLeastTwo input.squarefree input.elimination
    (Move.Track.Preparation.raw_windingFour sourceUnit targetUnit degree degreeTwo small index) assignment retained
  exact congrArg (fun owner => Fin.cast (unitTargetTrackCountEq targetUnit degree degreeTwo) owner) same

end Assignment

end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching.Preparation

end
