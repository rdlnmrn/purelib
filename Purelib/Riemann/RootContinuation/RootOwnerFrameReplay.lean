module
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Radius

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

@[expose] public section

/-! Restore the canonical endpoint frame, including its executable selector,
from a checked original isolation. The grid adapter retains the exact entry
list; pointwise-valid alternative owners are not substituted for that list. -/
namespace Purelib.Riemann.RootContinuation.RootOwnerFrameReplay.OwnerFrameReplay

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical} (nonzero : parameter ≠ 0)

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The exact two-root isolation output for the original square-root polynomial and canonical ambient. -/
abbrev Isolation := Exact.Basic.Output (SquareRootReconditioning.rootPolynomial parameter)
  (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter)) 2

/-- A retained isolation output certified equal to the original canonical isolation. -/
abbrev Saved := { output : Isolation (parameter := parameter) //
  output = (SquareRootReconditioning.isolationInput nonzero).isolation }

open Purelib.Data in
open Purelib.Polynomial in
/-- Restore both operational owners from the saved original isolation tracks. -/
def owners (saved : Saved nonzero) : Data.Vector (Owner parameter) 2 :=
  Vector.Basic.vectorOfFn fun index =>
    { parameterNonzero := nonzero
      ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter)
      track := saved.val.trackAt index }

open Purelib.Data in
/-- Every restored owner equals the canonical owner at the same original index. -/
theorem owners_eq (saved : Saved nonzero) (index : Fin 2) :
    owners nonzero saved index = SquareRootReconditioning.canonicalOwner nonzero index := by
  rw [owners, Vector.Basic.vectorOfFn_apply, saved.property]
  rfl

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Select a cached canonical owner through the original assignment and retained positive radius.

The common-track bridge preserves the exact owner index and operational root equivalence, with both strict containment
witnesses. -/
public def select
    (cachedOwners : Data.Vector (Owner parameter) 2)
    (canonical : ∀ index, cachedOwners index = SquareRootReconditioning.canonicalOwner nonzero index)
    (radius : Rat.Fraction.Rational) (positive : 0 < radius)
    (radius_eq : radius = Exact.Ownership.Radius.assignmentRadius (SquareRootReconditioning.rootPolynomial parameter)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter))
      (SquareRootReconditioning.isolationInput nonzero).isolation)
    (owner : Owner parameter) : OwnerSelection cachedOwners owner := by
  let assigned := SquareRootReconditioning.assignment nonzero owner
  let index : Fin 2 := assigned.owner.owner
  let refined := assigned.track.refine assigned.track.initial radius positive
  have commonStrict : assigned.track.initial.box.StrictInterior owner.track.initial.box := by
    rw [assigned.trackInitial]
    exact SquareRootReconditioning.assignment_state_strict_owner nonzero owner
  have freshStrict : refined.box.StrictInterior (cachedOwners index).track.initial.box := by
    rw [canonical index]
    change (assigned.track.refine assigned.track.initial radius positive).box.StrictInterior _
    subst radius
    exact assigned.owner.strict
  exact ⟨index, SquareRootTrackEquivalence.rootEquivalent_of_common_bridge nonzero
    owner.track assigned.track (cachedOwners index).track commonStrict radius positive refined rfl freshStrict⟩

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Restore the complete canonical frame from its saved original isolation.

Both owner entries and the executable selector use the retained isolation, assignment radius and exact canonical-owner
equations. -/
def restore (saved : Saved nonzero) : OwnerFrame parameter := by
  let radius := Exact.Ownership.Radius.assignmentRadius (SquareRootReconditioning.rootPolynomial parameter)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter)) saved.val
  have positive : 0 < radius := Exact.Ownership.Radius.assignmentRadius_pos _ _ _
  have radius_eq : radius = Exact.Ownership.Radius.assignmentRadius (SquareRootReconditioning.rootPolynomial parameter)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter))
      (SquareRootReconditioning.isolationInput nonzero).isolation := by
    unfold radius
    rw [saved.property]
    rfl
  refine ⟨owners nonzero saved, ?_, select nonzero (owners nonzero saved) (owners_eq nonzero saved) radius
    positive radius_eq⟩
  intro first second equivalent
  rw [owners_eq nonzero saved first, owners_eq nonzero saved second] at equivalent
  exact SquareRootTrackEquivalence.canonicalOwner_index_eq_of_rootEquivalent nonzero first second equivalent

/-- The restored frame equals the complete original canonical frame, including its executable selection function. -/
theorem restore_eq (saved : Saved nonzero) : restore nonzero saved = OwnerFrame.build nonzero := by
  rcases saved with ⟨output, same⟩
  cases same
  rfl

end Purelib.Riemann.RootContinuation.RootOwnerFrameReplay.OwnerFrameReplay

namespace Purelib.Riemann.RootContinuation.RootOwnerFrameReplay.RootFramesReplay

open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open _root_.Purelib.RootIsolation.SquareRoot.Grid.RootFrames (RootFrameEntry)
open Purelib.Data.Gaussian.Components.Basic (point)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

open Purelib.Data in
open Purelib.Polynomial in
/-- The original polynomial is nonzero at every retained vertical-horizontal grid intersection. -/
theorem pointNonzero (vertical : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (horizontal :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) :
    polynomial.eval (Gaussian.Components.Basic.point vertical.coordinate horizontal.coordinate) ≠ 0 :=
  (Geometry.ClearPath.ClearSegment.horizontal vertical.coordinate vertical.coordinate horizontal.coordinate
    vertical.inside.1 vertical.inside.2 vertical.inside.1 vertical.inside.2 horizontal.clearance).start_eval_ne_zero

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Pair an actual grid intersection with the supplied original-target owner frame. -/
def entry (vertical : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (horizontal :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)
    (frame : OwnerFrame (polynomial.eval (Gaussian.Components.Basic.point vertical.coordinate horizontal.coordinate))) :
      SquareRoot.Grid.RootFrames.RootFrameEntry polynomial :=
  ⟨point vertical.coordinate horizontal.coordinate, frame⟩

/-- A supplied canonical frame gives exactly the original frame entry for the same two grid lines. -/
theorem entry_eq (vertical : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (horizontal :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)
    (frame : OwnerFrame (polynomial.eval (Gaussian.Components.Basic.point vertical.coordinate horizontal.coordinate)))
    (same : frame = OwnerFrame.build (pointNonzero vertical horizontal)) :
    entry vertical horizontal frame = SquareRoot.Grid.RootFrames.RootFrameEntry.ofLines vertical horizontal := by
  cases same
  rfl

end

open Purelib.Polynomial
open Purelib.RootIsolation
/-- Restore a grid frame bank from its exact retained original entry list.

The supplied list equality transports the original coverage certificate without substituting merely pointwise-valid
owners. -/
def restore (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (entries : List
  (SquareRoot.Grid.RootFrames.RootFrameEntry polynomial))
    (same : entries = (RootIsolation.SquareRoot.Grid.RootFrames.build grid).entries) :
      RootIsolation.SquareRoot.Grid.RootFrames grid where
  entries := entries
  covers := by
    intro base member
    rw [same]
    exact (RootIsolation.SquareRoot.Grid.RootFrames.build grid).covers base member

/-- Restoring the exact original entry list gives the complete original grid frame bank. -/
theorem restore_eq (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (entries : List
  (SquareRoot.Grid.RootFrames.RootFrameEntry polynomial))
    (same : entries = (RootIsolation.SquareRoot.Grid.RootFrames.build grid).entries) : restore grid entries same =
      RootIsolation.SquareRoot.Grid.RootFrames.build grid := by
  cases same
  rfl

end Purelib.Riemann.RootContinuation.RootOwnerFrameReplay.RootFramesReplay
