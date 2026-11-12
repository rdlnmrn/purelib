module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
public import Purelib.Riemann.RootContinuation.RootPathTransport.RoundTrip
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

/-! # Signed entry of an actual owner at any point of a regular face

The original face frame, actual point owner and retained forward/backward
transports determine the selected sheet. The original anchor's reference
supplies the one needed round-trip law. No grid-vertex membership, desired
root relation or matrix/cycle agreement is required at the interior point.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib.Riemann.Paths

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {base : Canonical}

/-- Derive the original face entry from actual retained two-way transports and classification of this same old owner.

The supplied complete point frame classifies the actual owner. The reverse
target selects its original face sheet; the retained forward row then
reaches that same point-frame owner and the original source owner. Neither
transport, frame selection nor paid source trace is executed again here.
-/
def ofRoundTrip {owner : Owner (curve.polynomial.eval base)} (models : FaceModels frames face)
    (inside : face.cell.box.Contains base)
    (pointFrame : OwnerFrame (curve.polynomial.eval base))
    (outward : Route curve.polynomial face.cell.box face.cell.box.anchor base)
    (inward : Route curve.polynomial face.cell.box base face.cell.box.anchor)
    (forward : PathTransport outward.path models.frame pointFrame)
    (backward : PathTransport inward.path pointFrame models.frame)
    (selected : OwnerSelection pointFrame.owners owner) :
    Face.Entries.FaceModels.Entry models base owner := by
  have outwardWinding := Paths.ClearBoxPathWinding.Route.winding
    face.clearance (BranchIsolation.degreePositive curve) outward face.cell.box.contains_anchor
  have inwardWinding := Paths.ClearBoxPathWinding.Route.winding
    face.clearance (BranchIsolation.degreePositive curve) inward inside
  have cancel : PreparedPathWinding.ClearPath.rawWinding outward.path +
      PreparedPathWinding.ClearPath.rawWinding inward.path = 0 := by
    rewrite [outwardWinding, inwardWinding]
    omega0
  let reference := (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
    (face.cell.anchor_mem face.member)).toLoop
  let sheet := backward.target selected.index
  let row := forward.row sheet
  have target_eq : row.target = selected.index :=
    forward.reverseRoundTrip_index reference backward cancel selected.index
  have equivalent : NamedEquivalent (ownerName (pointFrame.owners row.target)) (ownerName owner) :=
    NamedEquivalent.transport
      (congrArg (fun index => ownerName (pointFrame.owners index)) target_eq).symm rfl selected.equivalent.symm
  have reached : Reached face.cell.box (models.frame.owners sheet) (pointFrame.owners row.target) :=
    ⟨row.joined, row.joined_winding.trans outwardWinding⟩
  exact ⟨sheet, reached.append (Face.Entries.Reached.ofEquivalent equivalent)⟩

/-- Retain the complete new interior-entry acquisition on the original supplied owner.

Each subtype stores one original factory result and its complete equality.
The original face frame remains models.frame; both routes, point frame,
transport rows, owner selection and resulting Entry are retained together.
This cache differs from Entry, whose reachability proof erases the auxiliary
transports and does not retain their execution results.
-/
@[expose] def Acquisition (models : FaceModels frames face) (inside : face.cell.box.Contains base)
    (owner : Owner (curve.polynomial.eval base)) : Type :=
  Σ pointFrame : {value : OwnerFrame (curve.polynomial.eval base) //
    value = OwnerFrame.build owner.parameterNonzero},
  Σ outward : {value : Route curve.polynomial face.cell.box face.cell.box.anchor base //
    value = Route.build face.clearance face.cell.box.anchor base face.cell.box.contains_anchor inside},
  Σ inward : {value : Route curve.polynomial face.cell.box base face.cell.box.anchor //
    value = Route.build face.clearance base face.cell.box.anchor inside face.cell.box.contains_anchor},
  Σ forward : {value : PathTransport outward.val.path models.frame pointFrame.val //
    value = PathTransport.build outward.val.path outward.val.within models.frame pointFrame.val},
  Σ backward : {value : PathTransport inward.val.path pointFrame.val models.frame //
    value = PathTransport.build inward.val.path inward.val.within pointFrame.val models.frame},
  Σ selected : {value : OwnerSelection pointFrame.val.owners owner //
    value = pointFrame.val.select owner},
  {value : Face.Entries.FaceModels.Entry models base owner //
    value = ofRoundTrip models inside pointFrame.val outward.val inward.val forward.val backward.val selected.val}

namespace Acquisition

variable {models : FaceModels frames face} {inside : face.cell.box.Contains base}
variable {owner : Owner (curve.polynomial.eval base)}

/-- Execute the new interior-entry factories once, retaining every complete result in its original order. -/
def build (models : FaceModels frames face) (inside : face.cell.box.Contains base)
    (owner : Owner (curve.polynomial.eval base)) : Acquisition models inside owner :=
  let pointFrame := OwnerFrame.build owner.parameterNonzero
  let outward := Route.build face.clearance face.cell.box.anchor base face.cell.box.contains_anchor inside
  let inward := Route.build face.clearance base face.cell.box.anchor inside face.cell.box.contains_anchor
  let forward := PathTransport.build outward.path outward.within models.frame pointFrame
  let backward := PathTransport.build inward.path inward.within pointFrame models.frame
  let selected := pointFrame.select owner
  let entry := ofRoundTrip models inside pointFrame outward inward forward backward selected
  ⟨⟨pointFrame, rfl⟩, ⟨outward, rfl⟩, ⟨inward, rfl⟩, ⟨forward, rfl⟩,
    ⟨backward, rfl⟩, ⟨selected, rfl⟩, ⟨entry, rfl⟩⟩

variable (acquired : Acquisition models inside owner)

/-- Read the same supplied face frame; this acquisition does not build a replacement. -/
@[expose] def faceFrame (_acquired : Acquisition models inside owner) :
    OwnerFrame (curve.polynomial.eval face.cell.box.anchor) := models.frame

/-- Read the complete cached frame at the actual supplied point. -/
@[expose] def pointFrame : OwnerFrame (curve.polynomial.eval base) := acquired.1.val

/-- Read the complete cached anchor-to-point route. -/
@[expose] def outward : Route curve.polynomial face.cell.box face.cell.box.anchor base := acquired.2.1.val

/-- Read the complete cached point-to-anchor route. -/
@[expose] def inward : Route curve.polynomial face.cell.box base face.cell.box.anchor := acquired.2.2.1.val

/-- Read both original retained forward transport rows between these exact frames. -/
@[expose] def forward : PathTransport acquired.outward.path models.frame acquired.pointFrame :=
  acquired.2.2.2.1.val

/-- Read both original retained reverse transport rows between these exact frames. -/
@[expose] def backward : PathTransport acquired.inward.path acquired.pointFrame models.frame :=
  acquired.2.2.2.2.1.val

/-- Read the cached original classification of this actual source owner. -/
@[expose] def selected : OwnerSelection acquired.pointFrame.owners owner := acquired.2.2.2.2.2.1.val

/-- Read the original Entry reached from the retained face sheet to this same actual owner. -/
@[expose] def entry : Face.Entries.FaceModels.Entry models base owner := acquired.2.2.2.2.2.2.val

/-- The retained point frame is the complete original factory output. -/
theorem pointFrame_eq : acquired.pointFrame = OwnerFrame.build owner.parameterNonzero := acquired.1.property

/-- The retained forward route is the complete original factory output. -/
theorem outward_eq : acquired.outward =
    Route.build face.clearance face.cell.box.anchor base face.cell.box.contains_anchor inside :=
  acquired.2.1.property

/-- The retained reverse route is the complete original factory output. -/
theorem inward_eq : acquired.inward =
    Route.build face.clearance base face.cell.box.anchor inside face.cell.box.contains_anchor :=
  acquired.2.2.1.property

/-- The retained forward bank is the complete original transport factory output. -/
theorem forward_eq : acquired.forward = PathTransport.build acquired.outward.path acquired.outward.within
    models.frame acquired.pointFrame := acquired.2.2.2.1.property

/-- The retained reverse bank is the complete original transport factory output. -/
theorem backward_eq : acquired.backward = PathTransport.build acquired.inward.path acquired.inward.within
    acquired.pointFrame models.frame := acquired.2.2.2.2.1.property

/-- The stored selection is the original frame selector's whole result. -/
theorem selected_eq : acquired.selected = acquired.pointFrame.select owner := acquired.2.2.2.2.2.1.property

/-- The stored Entry is the complete original-owner result of the retained round-trip data. -/
theorem entry_eq : acquired.entry = ofRoundTrip models inside acquired.pointFrame acquired.outward acquired.inward
    acquired.forward acquired.backward acquired.selected := acquired.2.2.2.2.2.2.property

/-- The retained original Entry selects the reverse transport's actual target index. -/
theorem sheet_eq : acquired.entry.sheet = acquired.backward.target acquired.selected.index :=
  (congrArg (fun value : Face.Entries.FaceModels.Entry models base owner => value.sheet)
    acquired.entry_eq).trans rfl

/-- The cached forward row on the retained sheet ends at the originally selected point-frame index.

The same regular-face clearance pays both cached route windings. The
original anchor reference and reverseRoundTrip_index then identify this
actual row's target; no new route, transport or owner selection is built.
-/
theorem target_eq : acquired.forward.target acquired.entry.sheet = acquired.selected.index := by
  have outwardWinding := Paths.ClearBoxPathWinding.Route.winding
    face.clearance (BranchIsolation.degreePositive curve) acquired.outward face.cell.box.contains_anchor
  have inwardWinding := Paths.ClearBoxPathWinding.Route.winding
    face.clearance (BranchIsolation.degreePositive curve) acquired.inward inside
  have cancel : PreparedPathWinding.ClearPath.rawWinding acquired.outward.path +
      PreparedPathWinding.ClearPath.rawWinding acquired.inward.path = 0 := by
    rewrite [outwardWinding, inwardWinding]
    omega0
  let reference := (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
    (face.cell.anchor_mem face.member)).toLoop
  rewrite [acquired.sheet_eq]
  exact acquired.forward.reverseRoundTrip_index reference acquired.backward cancel acquired.selected.index

/-- Compare the actual cached forward row's finish owner to the same supplied old owner.

Both operational comparisons come from retained selections: the forward
row's target selection and the original point-frame selection. Transport
uses only the derived equality of their actual indices. No observation,
refinement, route or continuation producer is executed here.
-/
def equivalent : NamedEquivalent
    (ownerName (acquired.forward.row acquired.entry.sheet).traced.finishOwner) (ownerName owner) := by
  let row := acquired.forward.row acquired.entry.sheet
  have target : row.target = acquired.selected.index := acquired.target_eq
  exact row.equivalent.trans (NamedEquivalent.transport
    (congrArg (fun index => ownerName (acquired.pointFrame.owners index)) target).symm rfl
    acquired.selected.equivalent.symm)

/-- Connect the retained face-sheet anchor to the exact supplied owner through its cached forward trace.

The only new handoff is the original stationary OwnerJoin paid by the
already derived acquired.equivalent. The point frame, route, transport row,
Entry and both endpoint Owners remain the supplied cached values.
-/
def anchorToOwner : OwnerPath curve.polynomial face.cell.box.anchor
    (models.frame.owners acquired.entry.sheet) base owner :=
  let row := acquired.forward.row acquired.entry.sheet
  row.traced.trace.get.append
    (OwnerPath.join curve.polynomial base row.traced.finishOwner owner acquired.equivalent)

/-- The connector retains the whole selected forward trace and its actual stationary finish handoff. -/
theorem anchorToOwner_eq : acquired.anchorToOwner =
    (acquired.forward.row acquired.entry.sheet).traced.trace.get.append
      (OwnerPath.join curve.polynomial base
        (acquired.forward.row acquired.entry.sheet).traced.finishOwner owner acquired.equivalent) := by rfl

/-- The forward connector preserves the actual open winding of its retained regular-face route. -/
theorem anchorToOwner_winding :
    chainRaw curve.polynomial face.cell.box.anchor acquired.anchorToOwner.vertices =
      PreparedPathWinding.ClearPath.rawWinding acquired.outward.path := by
  rewrite [acquired.anchorToOwner_eq, OwnerPath.append_winding,
    Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original,
    OwnerPath.join_winding, Int.add_zero]
  rfl

/-- Connect the supplied owner back to its retained face-sheet anchor through the cached reverse row.

The original selection compares the supplied Owner to its point-frame
Owner in that direction. The reverse row keeps its own trace and target
selection. Only the derived sheet equality reindexes the final Owner;
no reachability witness is extracted and no transport is prepared again.
-/
def ownerToAnchor : OwnerPath curve.polynomial base owner face.cell.box.anchor
    (models.frame.owners acquired.entry.sheet) :=
  let row := acquired.backward.row acquired.selected.index
  let initial := OwnerPath.join curve.polynomial base owner
    (acquired.pointFrame.owners acquired.selected.index) acquired.selected.equivalent
  (initial.append row.joined).reindexOwners rfl
    (congrArg (fun sheet => models.frame.owners sheet) acquired.sheet_eq.symm)

/-- The return connector preserves the complete reverse row and both actual stationary handoffs. -/
theorem ownerToAnchor_eq : acquired.ownerToAnchor =
    ((OwnerPath.join curve.polynomial base owner
      (acquired.pointFrame.owners acquired.selected.index) acquired.selected.equivalent).append
        (acquired.backward.row acquired.selected.index).joined).reindexOwners rfl
          (congrArg (fun sheet => models.frame.owners sheet) acquired.sheet_eq.symm) := by rfl

/-- The return connector preserves the actual open winding of its retained regular-face route. -/
theorem ownerToAnchor_winding :
    chainRaw curve.polynomial base acquired.ownerToAnchor.vertices =
      PreparedPathWinding.ClearPath.rawWinding acquired.inward.path := by
  let row := acquired.backward.row acquired.selected.index
  let initial := OwnerPath.join curve.polynomial base owner
    (acquired.pointFrame.owners acquired.selected.index) acquired.selected.equivalent
  have vertices := OwnerPath.reindexOwners_vertices rfl
    (congrArg (fun sheet => models.frame.owners sheet) acquired.sheet_eq.symm)
    (initial.append row.joined)
  have preserved := congrArg (chainRaw curve.polynomial base) vertices
  have appended := OwnerPath.append_winding initial row.joined
  have initialWinding := OwnerPath.join_winding curve.polynomial base owner
    (acquired.pointFrame.owners acquired.selected.index) acquired.selected.equivalent
  have replaced := congrArg (fun value : Int => value + chainRaw curve.polynomial base row.joined.vertices)
    initialWinding
  have finished := preserved.trans (appended.trans
    (replaced.trans ((Data.Int.Arithmetic.zero_add _).trans row.joined_winding)))
  exact finished

/-- Reindex the whole retained acquisition along actual point and Owner identities.

The point equality alone identifies no Owners. The separate heterogeneous
identity retains the same full Owner and every existing transport cache;
only their dependent indices and proof-irrelevant containment proof change.
-/
@[expose] def castPoint {first last : Canonical}
    {firstInside : face.cell.box.Contains first} {lastInside : face.cell.box.Contains last}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (original : Acquisition models firstInside firstOwner) : Acquisition models lastInside lastOwner := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  exact original

/-- Point/Owner reindexing preserves the complete original acquisition heterogeneously. -/
theorem castPoint_heq {first last : Canonical}
    {firstInside : face.cell.box.Contains first} {lastInside : face.cell.box.Contains last}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (original : Acquisition models firstInside firstOwner) :
    HEq (castPoint (lastInside := lastInside) samePoint sameOwner original) original := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  unfold castPoint
  rfl

/-- Reindexing keeps the exact selected sheet of that same complete acquisition. -/
theorem castPoint_sheet {first last : Canonical}
    {firstInside : face.cell.box.Contains first} {lastInside : face.cell.box.Contains last}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (original : Acquisition models firstInside firstOwner) :
    (castPoint (lastInside := lastInside) samePoint sameOwner original).entry.sheet = original.entry.sheet := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  unfold castPoint
  rfl

end Acquisition

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

end
