module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTracePath

/-! # Actual continued Points reached on the original selected face sheet

A new contained anchor route and its actual retained trace seed one
continued neighborhood and Point. The supplied target frame may be an
existing frame-bank extension entry; it is retained without replacement.
All selections compare the same stored trace and Point Owners. No final
signed relation or caller-provided continued neighborhood is required.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood (Neighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank}
variable (models : FaceModels frames face) (sheet : Fin 2) (point : Canonical)
variable (inside : face.cell.box.Contains point) (count : Nat)
variable (targetFrame : OwnerFrame (curve.polynomial.eval point))

/-- Retain one genuine trace, neighborhood, Point and all target-frame comparisons on the selected old face.

Every result has its whole original factory equality. The target frame is
an input cache (for example a RootFrames.extend entry), not a replacement
isolation hidden in a getter. The original nominal Point owner remains
separate from both traced finish and selected frame owners.
-/
@[expose] def TracedPoint : Type _ :=
  Σ frame : {value : OwnerFrame (curve.polynomial.eval point) // value = targetFrame},
  Σ route : {value : Route curve.polynomial face.cell.box face.cell.box.anchor point //
    value = Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor inside},
  Σ traced : {value : TracedPath route.val.path (models.frame.owners sheet) //
    value = TracedPath.build route.val.path route.val.within (models.frame.owners sheet)},
  Σ neighborhood : {value : Neighborhood traced.val count // value = Neighborhood.build traced.val count},
  Σ sample : {value : ContinuedNeighborhood.Point neighborhood.val.patch point //
    value = ContinuedNeighborhood.Point.acquire neighborhood.val.patch point neighborhood.val.center_inside},
  Σ equivalent : {value : NamedEquivalent (ownerName traced.val.finishOwner) (ownerName sample.val.owner) //
    value = neighborhood.val.pointEquivalent sample.val},
  Σ _row : {value : TransportRow route.val.path models.frame frame.val sheet //
    value = TransportRow.ofTraced frame.val traced.val},
  {selected : OwnerSelection frame.val.owners sample.val.owner // selected = frame.val.select sample.val.owner} ×
    {value : Entry models point sample.val.owner //
      value = ((Entry.origin models sheet).followTrace traced.val
        (InBox.ofWithin route.val.path route.val.within
          face.cell.box.contains_anchor)).followEquivalent equivalent.val}

namespace TracedPoint

/-- The exact retained cache suffix after an abstract original route and trace.

All six original values and their complete factory equations retain the
same dependent Sigma/Subtype layout. The input frame, route and traced
continuation are already supplied values, not factories to execute again.
-/
private def Tail (frame : OwnerFrame (curve.polynomial.eval point))
    (route : Route curve.polynomial face.cell.box face.cell.box.anchor point)
    (traced : TracedPath route.path (models.frame.owners sheet)) : Type _ :=
  Σ neighborhood : {value : Neighborhood traced count // value = Neighborhood.build traced count},
  Σ sample : {value : ContinuedNeighborhood.Point neighborhood.val.patch point //
    value = ContinuedNeighborhood.Point.acquire neighborhood.val.patch point neighborhood.val.center_inside},
  Σ equivalent : {value : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.val.owner) //
    value = neighborhood.val.pointEquivalent sample.val},
  Σ _row : {value : TransportRow route.path models.frame frame sheet // value = TransportRow.ofTraced frame traced},
  {selected : OwnerSelection frame.owners sample.val.owner // selected = frame.select sample.val.owner} ×
    {value : Entry models point sample.val.owner //
      value = ((Entry.origin models sheet).followTrace traced
        (InBox.ofWithin route.path route.within
          face.cell.box.contains_anchor)).followEquivalent equivalent.val}

/-- Execute the original ordered suffix factories once on the SAME supplied frame, route and trace.

The seed, Point, comparison, transport row, selector and Entry retain their
whole original equations. No prefix factory or original cache is rebuilt.
-/
private def buildTail (frame : OwnerFrame (curve.polynomial.eval point))
    (route : Route curve.polynomial face.cell.box face.cell.box.anchor point)
    (traced : TracedPath route.path (models.frame.owners sheet)) :
    Tail (models := models) (sheet := sheet) (point := point) (count := count) frame route traced :=
  let neighborhood := Neighborhood.build traced count
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch point neighborhood.center_inside
  let equivalent : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.owner) :=
    neighborhood.pointEquivalent sample
  let row := TransportRow.ofTraced frame traced
  let selected := frame.select sample.owner
  let entry := ((Entry.origin models sheet).followTrace traced
    (InBox.ofWithin route.path route.within
      face.cell.box.contains_anchor)).followEquivalent equivalent
  ⟨⟨neighborhood, rfl⟩, ⟨sample, rfl⟩, ⟨equivalent, rfl⟩, ⟨row, rfl⟩, ⟨selected, rfl⟩, ⟨entry, rfl⟩⟩

/-- Construct one genuinely new point from a retained old anchor Owner and a supplied actual target frame.

The contained route and trace are new work. Neighborhood.build uses that
exact trace's terminal Owner; Point.acquire runs once at its certified
center. ofTraced reuses the same trace for the original transport row.
-/
def build {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank}
    (models : FaceModels frames face) (sheet : Fin 2) (point : Canonical)
    (inside : face.cell.box.Contains point) (count : Nat)
    (targetFrame : OwnerFrame (curve.polynomial.eval point)) :
    TracedPoint models sheet point inside count targetFrame :=
  let route := Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor inside
  let traced := TracedPath.build route.path route.within (models.frame.owners sheet)
  let tail := buildTail (models := models) (sheet := sheet) (point := point) (count := count)
    targetFrame route traced
  ⟨⟨targetFrame, rfl⟩, ⟨route, rfl⟩, ⟨traced, rfl⟩, tail⟩

variable {models sheet point inside count targetFrame}
variable (cached : TracedPoint models sheet point inside count targetFrame)

/-- Read the whole supplied frame cache. -/
def frame : OwnerFrame (curve.polynomial.eval point) := cached.1.val

/-- Read the actual newly prepared anchor-to-point route. -/
def route : Route curve.polynomial face.cell.box face.cell.box.anchor point := cached.2.1.val

/-- Read the one actual traced continuation from the retained original anchor Owner. -/
def traced : TracedPath cached.route.path (models.frame.owners sheet) := cached.2.2.1.val

/-- Read the one actual terminal-owner-seeded continued neighborhood. -/
def neighborhood : Neighborhood cached.traced count := cached.2.2.2.1.val

/-- Read the whole original acquired Point, including its actual root Owner and seed refinement. -/
def sample : ContinuedNeighborhood.Point cached.neighborhood.patch point := cached.2.2.2.2.1.val

/-- Read the actual cached traced-finish-to-Point comparison. -/
def equivalent : NamedEquivalent (ownerName cached.traced.finishOwner) (ownerName cached.sample.owner) :=
  cached.2.2.2.2.2.1.val

/-- Read the row reusing that exact retained trace and its own target-frame selection. -/
def row : TransportRow cached.route.path models.frame cached.frame sheet := cached.2.2.2.2.2.2.1.val

/-- Read the retained actual Point-to-frame selection. -/
def selected : OwnerSelection cached.frame.owners cached.sample.owner := cached.2.2.2.2.2.2.2.1.val

/-- Read the original face Entry derived for the SAME cached Point Owner. -/
def entry : Entry models point cached.sample.owner := cached.2.2.2.2.2.2.2.2.val

/-- The whole supplied target frame is retained unchanged. -/
theorem frame_eq : cached.frame = targetFrame := cached.1.property

/-- The retained route is the whole original contained connector factory. -/
theorem route_eq : cached.route =
    Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor inside := cached.2.1.property

/-- The retained trace is the whole actual original continuation factory. -/
theorem traced_eq : cached.traced = TracedPath.build cached.route.path cached.route.within
    (models.frame.owners sheet) := cached.2.2.1.property

/-- The neighborhood keeps its actual terminal-owner-seeded factory. -/
theorem neighborhood_eq : cached.neighborhood = Neighborhood.build cached.traced count := cached.2.2.2.1.property

/-- The Point keeps its exact once-executed original center acquisition. -/
theorem sample_eq : cached.sample = ContinuedNeighborhood.Point.acquire cached.neighborhood.patch point
    cached.neighborhood.center_inside := cached.2.2.2.2.1.property

/-- The actual Point comparison is its original cached seed/refinement constructor. -/
theorem equivalent_eq : cached.equivalent = cached.neighborhood.pointEquivalent cached.sample :=
  cached.2.2.2.2.2.1.property

/-- The row is the whole original ofTraced result on the SAME stored trace. -/
theorem row_eq : cached.row = TransportRow.ofTraced cached.frame cached.traced := cached.2.2.2.2.2.2.1.property

/-- The selected Point index is the original retained frame-selector result. -/
theorem selected_eq : cached.selected = cached.frame.select cached.sample.owner :=
  cached.2.2.2.2.2.2.2.1.property

/-- The derived Point Entry uses the SAME actual trace and Point comparison. -/
theorem entry_eq : cached.entry = ((Entry.origin models sheet).followTrace cached.traced
    (InBox.ofWithin cached.route.path cached.route.within
      face.cell.box.contains_anchor)).followEquivalent cached.equivalent := cached.2.2.2.2.2.2.2.2.property

/-- The actual cached Point retains the selected original face sheet. -/
theorem entry_sheet : cached.entry.sheet = sheet :=
  (congrArg Entry.sheet cached.entry_eq).trans
    ((((Entry.origin models sheet).followTrace cached.traced
      (InBox.ofWithin cached.route.path cached.route.within
        face.cell.box.contains_anchor)).followEquivalent_sheet cached.equivalent).trans
      ((Entry.origin models sheet).followTrace_sheet cached.traced
        (InBox.ofWithin cached.route.path cached.route.within
          face.cell.box.contains_anchor)))

/-- The two actual selections of this SAME traced finish and Point agree in the SAME retained frame.

Both operational comparisons are stored values. The original frame's
distinction law proves only an index equality; no root equality follows
from matching coordinates and no comparison producer is rerun.
-/
theorem target_eq : cached.row.target = cached.selected.index := by
  have traced : cached.row.traced = cached.traced :=
    (congrArg (fun value : TransportRow cached.route.path models.frame cached.frame sheet => value.traced)
      cached.row_eq).trans rfl
  exact cached.frame.distinguish _ _ (cached.row.equivalent.symm.trans
    ((NamedEquivalent.transport
      (congrArg (fun value : TracedPath cached.route.path (models.frame.owners sheet) =>
        ownerName value.finishOwner) traced).symm rfl cached.equivalent).trans
      cached.selected.equivalent))

/-- A contained trace from an actual source Entry selects this SAME cached Point occurrence.

The source Entry's retained reachability is eliminated only inside this
proposition. The original old-anchor reference and contained-path winding
law identify the two actual target-frame indices. No path is extracted
from a proposition into an executable comparison or new trace.
-/
theorem sourceTarget_eq {source : Canonical}
    {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
    (sourceEntry : Entry models source (sourceFrame.owners index))
    (same : sourceEntry.sheet = sheet) (sourceInside : face.cell.box.Contains source)
    (sourceRoute : Route curve.polynomial face.cell.box source point)
    (row : TransportRow sourceRoute.path sourceFrame cached.frame index) :
    row.target = cached.selected.index := by
  let arrived := sourceEntry.followTrace row.traced
    (InBox.ofWithin sourceRoute.path sourceRoute.within sourceInside)
  have arrivedSheet : arrived.sheet = sheet :=
    (sourceEntry.followTrace_sheet row.traced
      (InBox.ofWithin sourceRoute.path sourceRoute.within sourceInside)).trans same
  have reached : Reached face.cell.box (models.frame.owners sheet) row.traced.finishOwner :=
    Eq.mp (congrArg (fun value => Reached face.cell.box (models.frame.owners value)
      row.traced.finishOwner) arrivedSheet) arrived.reached
  obtain ⟨path, winding⟩ := reached
  have selected := RootContinuation.ClearBoxRootTransport.TracedPath.selection_eq_of_ownerPath
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop cached.route.within cached.traced path cached.frame
    (cached.frame.select cached.traced.finishOwner) row.selected
    ((Paths.ClearBoxPathWinding.Route.winding face.clearance (BranchIsolation.degreePositive curve)
      cached.route face.cell.box.contains_anchor).trans winding.symm)
  have target : cached.row.target = (cached.frame.select cached.traced.finishOwner).index :=
    congrArg (fun value : TransportRow cached.route.path models.frame cached.frame sheet => value.target)
      cached.row_eq
  exact (target.trans selected).symm.trans cached.target_eq

/-- Compare an actual contained source trace's finish to the SAME cached Point Owner.

The executable comparison composes the two stored selections after the
proved index equality. Both original Owners and their actual comparison
programs remain; reachability contributes only the erased index proof.
-/
def sourceEquivalent {source : Canonical}
    {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
    (sourceEntry : Entry models source (sourceFrame.owners index))
    (same : sourceEntry.sheet = sheet) (sourceInside : face.cell.box.Contains source)
    (sourceRoute : Route curve.polynomial face.cell.box source point)
    (row : TransportRow sourceRoute.path sourceFrame cached.frame index) :
    NamedEquivalent (ownerName row.traced.finishOwner) (ownerName cached.sample.owner) :=
  let equal := cached.sourceTarget_eq sourceEntry same sourceInside sourceRoute row
  row.equivalent.trans (NamedEquivalent.transport
    (congrArg (fun value => ownerName (cached.frame.owners value)) equal).symm rfl
    cached.selected.equivalent.symm)

/-- An exact whole-frame readback retained as data for optional selector reuse. -/
abbrev FrameReadback (frame : OwnerFrame (curve.polynomial.eval point)) :=
  {_value : Unit // frame = cached.frame}

/-- Reuse a stored Point selector only under equality of the complete actual frame; otherwise select once.

The optional equality is an exact frame-cache readback, not a desired
root relation. A present readback transports the SAME original selection;
an absent readback performs one genuine classification of the old Point.
-/
def selectionAt (frame : OwnerFrame (curve.polynomial.eval point)) (reuse : Option (cached.FrameReadback frame)) :
    OwnerSelection frame.owners cached.sample.owner :=
  match reuse with
  | some same => Eq.mpr (congrArg (fun value : OwnerFrame (curve.polynomial.eval point) =>
      OwnerSelection value.owners cached.sample.owner) same.property) cached.selected
  | none => frame.select cached.sample.owner

/-- A whole-frame readback reuses the SAME original selected value, changing only its dependent frame index. -/
theorem selectionAt_reuse_heq (frame : OwnerFrame (curve.polynomial.eval point)) (same : frame = cached.frame) :
    HEq (cached.selectionAt frame (some ⟨(), same⟩)) cached.selected := by
  cases same
  rfl

/-- The reused selector retains its original complete target-frame factory equation.

The whole frame equality transports the SAME cached selection and its
existing selected_eq certificate. The displayed selector is only the
factory readback; no classification executes in this proof.
-/
theorem selectionAt_reuse_eq (frame : OwnerFrame (curve.polynomial.eval point))
    (same : frame = cached.frame) :
    cached.selectionAt frame (some ⟨(), same⟩) = frame.select cached.sample.owner := by
  cases same
  change cached.selected = cached.frame.select cached.sample.owner
  exact cached.selected_eq

/-- The absent-readback branch is one genuine original classification of this SAME retained Point Owner. -/
theorem selectionAt_new (frame : OwnerFrame (curve.polynomial.eval point)) :
    cached.selectionAt frame none = frame.select cached.sample.owner := by rfl

/-- Retain both complete original caches, the actual reuse branch and one whole selection with its derived Entry.

The Point's neighborhood/count, original anchor trace and old target frame
remain inside the retained TracedPoint. No Point or trace is acquired here.
-/
abbrev FrameSelection (frame : OwnerFrame (curve.polynomial.eval point))
    (reuse : Option (cached.FrameReadback frame)) :=
  {value : TracedPoint models sheet point inside count targetFrame ×
      OwnerFrame (curve.polynomial.eval point) × Option (cached.FrameReadback frame) //
      value = (cached, frame, reuse)} ×
  (Σ selected : {value : OwnerSelection frame.owners cached.sample.owner // value = cached.selectionAt frame reuse},
  {value : Entry models point (frame.owners selected.val.index) //
    value = cached.entry.followEquivalent selected.val.equivalent})

/-- Retain one actual reused or newly executed selector and the original Entry transported through its comparison. -/
def selectFrame (frame : OwnerFrame (curve.polynomial.eval point)) (reuse : Option (cached.FrameReadback frame)) :
    cached.FrameSelection frame reuse :=
  let selected := cached.selectionAt frame reuse
  let entry := cached.entry.followEquivalent selected.equivalent
  (⟨(cached, frame, reuse), rfl⟩, ⟨⟨selected, rfl⟩, ⟨entry, rfl⟩⟩)

namespace FrameSelection

variable {cached} {frame : OwnerFrame (curve.polynomial.eval point)} {reuse : Option (cached.FrameReadback frame)}
variable (attached : cached.FrameSelection frame reuse)

/-- Read the whole original Point preparation, without executing a type-index factory. -/
def original : TracedPoint models sheet point inside count targetFrame := attached.1.val.1

/-- Read the whole actual target frame retained by this attachment. -/
def target : OwnerFrame (curve.polynomial.eval point) := attached.1.val.2.1

/-- Read the actual cached reuse/new-selection branch. -/
def mode : Option (cached.FrameReadback frame) := attached.1.val.2.2

/-- Read the complete reused or genuinely new original OwnerSelection. -/
def selected : OwnerSelection frame.owners cached.sample.owner := attached.2.1.val

/-- Read the original Point Entry followed through that SAME stored selector comparison. -/
def entry : Entry models point (frame.owners attached.selected.index) := attached.2.2.val

/-- All original Point data remain literally retained. -/
theorem original_eq : attached.original = cached := congrArg Prod.fst attached.1.property

/-- The whole target frame remains the supplied actual bank cache. -/
theorem target_eq : attached.target = frame := congrArg (fun value => value.2.1) attached.1.property

/-- The retained branch is its actual first-match frame-readback decision. -/
theorem mode_eq : attached.mode = reuse := congrArg (fun value => value.2.2) attached.1.property

/-- The whole selected value retains the exact reuse or genuine-classification factory. -/
theorem selected_eq : attached.selected = cached.selectionAt frame reuse := attached.2.1.property

/-- The derived Entry keeps the SAME cached comparison and whole original Entry. -/
theorem entry_eq : attached.entry = cached.entry.followEquivalent attached.selected.equivalent :=
  attached.2.2.property

/-- Reindexing the Point to its actual selected frame owner preserves its original face sheet. -/
theorem entry_sheet : attached.entry.sheet = sheet :=
  (congrArg Entry.sheet attached.entry_eq).trans
    ((cached.entry.followEquivalent_sheet attached.selected.equivalent).trans cached.entry_sheet)

end FrameSelection

/-- An actual contained source row agrees with the attached Point's selected index in its actual new frame.

The original old-anchor reference compares the retained anchor trace with
reachability of this actual row. The two selections are existing values;
no selector, trace or computational path is extracted from a proposition.
-/
theorem sourceFrameTarget_eq {ambient : Geometry.Rational.Box} {source : Canonical}
    {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient source point}
    (sourceEntry : Entry models source (sourceFrame.owners index))
    (same : sourceEntry.sheet = sheet) (contained : InBox face.cell.box path)
    (frame : OwnerFrame (curve.polynomial.eval point))
    (selected : OwnerSelection frame.owners cached.sample.owner)
    (row : TransportRow path sourceFrame frame index) : row.target = selected.index := by
  let arrived := sourceEntry.followTrace row.traced contained
  have arrivedSheet : arrived.sheet = sheet := (sourceEntry.followTrace_sheet row.traced contained).trans same
  have reached : Reached face.cell.box (models.frame.owners sheet) row.traced.finishOwner :=
    Eq.mp (congrArg (fun value => Reached face.cell.box (models.frame.owners value)
      row.traced.finishOwner) arrivedSheet) arrived.reached
  obtain ⟨actualPath, winding⟩ := reached
  let fromAnchor : OwnerSelection frame.owners cached.traced.finishOwner :=
    ⟨selected.index, cached.equivalent.trans selected.equivalent⟩
  have equal := RootContinuation.ClearBoxRootTransport.TracedPath.selection_eq_of_ownerPath
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop cached.route.within cached.traced actualPath frame
    fromAnchor row.selected
    ((Paths.ClearBoxPathWinding.Route.winding face.clearance (BranchIsolation.degreePositive curve)
      cached.route face.cell.box.contains_anchor).trans winding.symm)
  exact equal.symm

/-- Compare an actual contained row finish to the SAME retained Point using both actual target selections. -/
def sourceFrameEquivalent {ambient : Geometry.Rational.Box} {source : Canonical}
    {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient source point}
    (sourceEntry : Entry models source (sourceFrame.owners index))
    (same : sourceEntry.sheet = sheet) (contained : InBox face.cell.box path)
    (frame : OwnerFrame (curve.polynomial.eval point))
    (selected : OwnerSelection frame.owners cached.sample.owner)
    (row : TransportRow path sourceFrame frame index) :
    NamedEquivalent (ownerName row.traced.finishOwner) (ownerName cached.sample.owner) :=
  let equal := cached.sourceFrameTarget_eq sourceEntry same contained frame selected row
  row.equivalent.trans (NamedEquivalent.transport
    (congrArg (fun value => ownerName (frame.owners value)) equal).symm rfl selected.equivalent.symm)

end TracedPoint

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

end
