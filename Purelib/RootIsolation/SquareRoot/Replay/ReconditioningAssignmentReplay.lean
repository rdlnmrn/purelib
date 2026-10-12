module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Exact.Ownership.Replay
import Purelib.RootIsolation.Residual.Global.Assignment
public import Purelib.RootIsolation.Residual.Global.Replay

import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
public import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-! Restore the original endpoint classifier from its exact sample and
residual assignment. The retained index is the original partition selection. -/
namespace Purelib.RootIsolation.SquareRoot.Replay.ReconditioningAssignmentReplay

variable {parameter : Riemann.RootContinuation.SquareRootReconditioning.Gaussian} (nonzero : parameter ≠ 0) (owner :
  Riemann.RootContinuation.SquareRootReconditioning.Owner parameter)

/-- A retained exact Gaussian sample equal to the original owner's reconditioning sample. -/
abbrev Sample := {point : Riemann.RootContinuation.SquareRootReconditioning.Gaussian // point =
  Riemann.RootContinuation.SquareRootReconditioning.sample nonzero owner}

/-- The retained reconditioning sample belongs to the original quadratic isolation square. -/
theorem inside (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) :
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial parameter)).Contains saved.val := by
  rw [saved.property]
  exact Riemann.RootContinuation.SquareRootReconditioning.sample_inside_largeSquare nonzero owner

/-- The retained sample satisfies the original owner's requested global-localization residual target. -/
theorem residual (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) :
    Data.Gaussian.Norm.Basic.normSq ((Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial
      parameter).eval saved.val) <
      Residual.Global.Assignment.insideResidualTarget (Riemann.RootContinuation.SquareRootReconditioning.isolationInput
        nonzero) (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius owner) := by
  rw [saved.property]
  have scalar := Riemann.RootContinuation.SquareRootReconditioning.sample_residual_lt_insideTarget nonzero owner
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact scalar

/-- The original assignment-track ownership replay certificate for this exact retained sample. -/
abbrev Refined (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) :=
  Residual.Global.Replay.Refined (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero) saved.val
    (SquareRoot.Replay.ReconditioningAssignmentReplay.inside nonzero owner saved)
      (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius_positive owner)
      (SquareRoot.Replay.ReconditioningAssignmentReplay.residual nonzero owner saved)

/-- Restore the original global residual assignment using the retained sample and ownership replay certificate. -/
def restore (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :=
  Residual.Global.Replay.restore (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero) saved.val
    (SquareRoot.Replay.ReconditioningAssignmentReplay.inside nonzero owner saved)
      (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius_positive owner)
      (SquareRoot.Replay.ReconditioningAssignmentReplay.residual nonzero owner saved) refined

/-- The original quadratic assignment result at the owner's computed reconditioning sample and requested radius. -/
abbrev Assignment := Residual.Global.Assignment.AssignedResult
  (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero)
  (Riemann.RootContinuation.SquareRootReconditioning.sample nonzero owner)
    (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius owner)

/-- Transport the restored assignment along the retained exact sample equality. -/
def assigned (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Assignment nonzero owner :=
  cast (congrArg (fun point : Riemann.RootContinuation.SquareRootReconditioning.Gaussian =>
    Residual.Global.Assignment.AssignedResult (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero)
    point (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius owner)) saved.property)
      (SquareRoot.Replay.ReconditioningAssignmentReplay.restore nonzero owner saved refined)

/-- The restored and transported assignment equals the original reconditioning assignment exactly. -/
theorem assigned_eq (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
    SquareRoot.Replay.ReconditioningAssignmentReplay.assigned nonzero owner saved refined =
      Riemann.RootContinuation.SquareRootReconditioning.assignment nonzero owner := by
  rcases saved with ⟨point, same⟩
  cases same
  unfold SquareRoot.Replay.ReconditioningAssignmentReplay.assigned
    SquareRoot.Replay.ReconditioningAssignmentReplay.restore
    Riemann.RootContinuation.SquareRootReconditioning.assignment
  exact Residual.Global.Replay.restore_eq _ _ _ _ _ refined

/-- Select the original canonical frame owner using the restored assignment and its retained common refinement.

Keep the assignment's actual owner index and bridge state, and bind the supplied frame to its original constructor. -/
def selectAssigned (frame : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame parameter)
    (frameEq : frame = Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build nonzero) (value :
      SquareRoot.Replay.ReconditioningAssignmentReplay.Assignment nonzero owner) (same : value =
      Riemann.RootContinuation.SquareRootReconditioning.assignment nonzero owner)
    (refined : Exact.Ownership.Replay.Refined (Riemann.RootContinuation.SquareRootReconditioning.isolationInput
      nonzero).isolation value.track) :
    Riemann.RootContinuation.RootOwnerFrames.OwnerSelection frame.owners owner := by
  let index : Fin 2 := value.owner.owner
  let radius := Exact.Ownership.Radius.assignmentRadius
    (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial parameter)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial parameter))
      (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero).isolation
  have positive : 0 < radius := Exact.Ownership.Radius.assignmentRadius_pos _ _ _
  have commonStrict : value.track.initial.box.StrictInterior owner.track.initial.box := by
    rw [same, (Riemann.RootContinuation.SquareRootReconditioning.assignment nonzero owner).trackInitial]
    exact Riemann.RootContinuation.SquareRootReconditioning.assignment_state_strict_owner nonzero owner
  have freshStrict : refined.val.box.StrictInterior
      (frame.owners index).track.initial.box := by
    rw [frameEq, show (Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build nonzero).owners index =
      Riemann.RootContinuation.SquareRootReconditioning.canonicalOwner nonzero index from
      Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.canonicalOwners_eq nonzero index]
    rw [refined.property]
    exact value.owner.strict
  exact ⟨index, Riemann.RootContinuation.SquareRootTrackEquivalence.rootEquivalent_of_common_bridge nonzero
    owner.track value.track (frame.owners index).track
    commonStrict radius positive refined.val refined.property freshStrict⟩

/-- Selection from the restored assignment equals the original frame's owner selection exactly. -/
theorem selectAssigned_eq (frame : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame parameter)
    (frameEq : frame = Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build nonzero) (value :
      SquareRoot.Replay.ReconditioningAssignmentReplay.Assignment nonzero owner) (same : value =
      Riemann.RootContinuation.SquareRootReconditioning.assignment nonzero owner)
    (refined : Exact.Ownership.Replay.Refined (Riemann.RootContinuation.SquareRootReconditioning.isolationInput
      nonzero).isolation value.track) :
    SquareRoot.Replay.ReconditioningAssignmentReplay.selectAssigned nonzero owner frame frameEq value same refined =
      frame.select owner := by
  cases frameEq
  cases same
  rcases refined with ⟨state, equal⟩
  cases equal
  rfl

/-- The restored assignment retains exactly the reconstructed global replay track. -/
theorem assigned_track (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
    (SquareRoot.Replay.ReconditioningAssignmentReplay.assigned nonzero owner saved refined).track =
      Residual.Global.Replay.track (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero) saved.val
        (SquareRoot.Replay.ReconditioningAssignmentReplay.inside nonzero owner saved)
          (Riemann.RootContinuation.SquareRootReconditioning.requestedRadius_positive owner)
          (SquareRoot.Replay.ReconditioningAssignmentReplay.residual nonzero owner saved) := by
  rcases saved with ⟨point, same⟩
  cases same
  rfl

/-- Transport the retained ownership replay certificate to the restored assignment's exact track. -/
def assignedRefined (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
  SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
    Exact.Ownership.Replay.Refined (Riemann.RootContinuation.SquareRootReconditioning.isolationInput nonzero).isolation
      (SquareRoot.Replay.ReconditioningAssignmentReplay.assigned nonzero owner saved refined).track :=
  ⟨refined.val, by rw [SquareRoot.Replay.ReconditioningAssignmentReplay.assigned_track]; exact refined.property⟩

/-- Restore the retained assignment and select its owner in the original canonical frame. -/
def select (frame : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame parameter)
    (frameEq : frame = Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build nonzero)
    (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
      SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
    Riemann.RootContinuation.RootOwnerFrames.OwnerSelection frame.owners owner :=
  SquareRoot.Replay.ReconditioningAssignmentReplay.selectAssigned nonzero owner frame frameEq
    (SquareRoot.Replay.ReconditioningAssignmentReplay.assigned nonzero owner saved refined)
    (SquareRoot.Replay.ReconditioningAssignmentReplay.assigned_eq nonzero owner saved refined)
      (SquareRoot.Replay.ReconditioningAssignmentReplay.assignedRefined nonzero owner saved refined)

/-- Replay-based frame selection returns exactly the original frame's owner selection. -/
theorem select_eq (frame : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame parameter)
    (frameEq : frame = Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build nonzero)
    (saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner) (refined :
      SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner saved) :
    SquareRoot.Replay.ReconditioningAssignmentReplay.select nonzero owner frame frameEq saved refined = frame.select
      owner :=
  SquareRoot.Replay.ReconditioningAssignmentReplay.selectAssigned_eq nonzero owner frame frameEq _ _ _

end Purelib.RootIsolation.SquareRoot.Replay.ReconditioningAssignmentReplay
