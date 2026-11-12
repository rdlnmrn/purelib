module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames

/-! # Actual Point entries in the retained local framed bank

An existing walk and the same cached bank rows derive the face sheet of
an actual fine-frame Owner. A genuine new classification attaches a
supplied original Point to that frame, retaining the whole old inputs and
selection. This is signed incidence, not mesh deformation or normalization.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member}

namespace CellRows

variable {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} (retained : CellRows old face coarse cuts)
variable (models : FaceModels frames face)

/-- The stored old-anchor frame equality gives the literal original Entry on the SAME fine frame Owner. -/
private def originEntry (member : FromStates.ContainsVertex retained.grid face.cell.box.anchor) (index : Fin 2) :
    Entry models face.cell.box.anchor ((retained.localFrames.frameAt face.cell.box.anchor member).owners index) := by
  have localFrame := (congrArg (fun value : RootFrames retained.grid =>
    value.frameAt face.cell.box.anchor member) retained.localFrames_eq).trans
    (frames.extend_frameAt retained.grid face.cell.box.anchor member (face.cell.anchor_mem face.member))
  have ownerEq := congrArg (fun value : OwnerFrame (curve.polynomial.eval face.cell.box.anchor) =>
    value.owners index) (models.frame_eq.trans localFrame.symm)
  exact ⟨index, (Entry.origin models index).reached.castFinish rfl (heq_of_eq ownerEq)⟩

/-- Derive an Entry for either actual fine-frame Owner using one retained contained stem.

The original reverse target determines its old-anchor sheet. The original
anchored inverse law restores the requested finishing frame index. No
fine-vertex reference loop, Entry acquisition or signed relation is supplied.
-/
def atVertex {point : Canonical} (stem : Walks.Walk retained.grid face.cell.box.anchor point)
    (member : FromStates.ContainsVertex retained.grid point) (index : Fin 2) :
    Entry models point ((retained.localFrames.frameAt point member).owners index) := by
  let anchor := FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid
  let source := EdgeBank.RootEdgeBank.target retained.edges stem.reverse index
  let first := retained.originEntry models anchor source
  let inside := InBox.ofWithin stem.path stem.withinAmbient anchor.inside
  let arrived := Entry.followWalk (models := models) retained.edges stem anchor member inside source first
  have sheetEq := Entry.followWalk_sheet (models := models) retained.edges stem anchor member inside source first
  have reached : Reached face.cell.box (models.frame.owners source)
      ((retained.localFrames.frameAt point member).owners (EdgeBank.RootEdgeBank.target retained.edges stem source)) :=
    Eq.mp (congrArg (fun sheet => Reached face.cell.box (models.frame.owners sheet)
      ((retained.localFrames.frameAt point member).owners (EdgeBank.RootEdgeBank.target retained.edges stem source)))
      sheetEq) arrived.reached
  have restored := EdgeBank.RootEdgeBank.target_reverse_right_anchored retained.edges
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop anchor stem index
  exact ⟨source, reached.castFinish rfl
    (heq_of_eq (congrArg (fun value => (retained.localFrames.frameAt point member).owners value) restored))⟩

/-- The original target maps compute this actual vertex Owner's old face-sheet index. -/
theorem atVertex_sheet {point : Canonical} (stem : Walks.Walk retained.grid face.cell.box.anchor point)
    (member : FromStates.ContainsVertex retained.grid point) (index : Fin 2) :
    (retained.atVertex models stem member index).sheet =
      EdgeBank.RootEdgeBank.target retained.edges stem.reverse index := by
  rfl

/-- Attach an actual retained lifted vertex index to its old face Entry through the SAME supplied stem.

The original VertexBank.owner definition reads the whole cached frame at
that literal index's coordinate and sheet. No coordinate-based owner
comparison or new vertex bank is introduced.
-/
def indexedEntry (vertices : VertexBank retained.grid) (index : Fin vertices.count)
    (stem : Walks.Walk retained.grid face.cell.box.anchor (vertices.coordinate index)) :
    Entry models (vertices.coordinate index) (vertices.owner retained.localFrames index) :=
  retained.atVertex models stem (vertices.coordinate_onGrid index) (vertices.sheet index)

section Point

variable {point : Canonical} (stem : Walks.Walk retained.grid face.cell.box.anchor point)
variable (member : FromStates.ContainsVertex retained.grid point)
variable {count : Nat} {neighborhood : ContinuedNeighborhood curve.polynomial count}
variable (sample : ContinuedNeighborhood.Point neighborhood point)

/-- Attach the SAME supplied Point to an actual fine frame using its complete retained classification.

The classification direction is Point Owner to selected frame Owner.
Reversing that actual relation carries the derived frame Entry back to
this original Point; no Owner equality follows from their common point.
-/
def entryFromSelection (selected : OwnerSelection (retained.localFrames.frameAt point member).owners sample.owner) :
    Entry models point sample.owner :=
  let original := retained.atVertex models stem member selected.index
  ⟨original.sheet, original.reached.append (Face.Entries.Reached.ofEquivalent selected.equivalent.symm)⟩

/-- One actual Point classification retains the whole old stem, Point and defining factory results. -/
abbrev PointEntry :=
  {value : Walks.Walk retained.grid face.cell.box.anchor point × ContinuedNeighborhood.Point neighborhood point //
    value = (stem, sample)} ×
  (Σ selected : {value : OwnerSelection (retained.localFrames.frameAt point member).owners sample.owner //
      value = (retained.localFrames.frameAt point member).select sample.owner},
  {value : Entry models point sample.owner //
    value = retained.entryFromSelection models stem member sample selected.val})

/-- Classify the existing Point once and derive its original face Entry through the SAME cached bank.

This finite selection is genuinely new comparison work. The old stem,
Point, query, Entry acquisition, mesh, root rows and observations are
neither rerun nor replaced; no final signed relation is an input.
-/
def classifyPoint : retained.PointEntry models stem member sample :=
  let selected := (retained.localFrames.frameAt point member).select sample.owner
  let entry := retained.entryFromSelection models stem member sample selected
  (⟨(stem, sample), rfl⟩, ⟨⟨selected, rfl⟩, ⟨entry, rfl⟩⟩)

namespace PointEntry

variable {retained models stem member sample} (classified : retained.PointEntry models stem member sample)

/-- Read the complete original Point, retaining its Owner, seed refinement and cached parameter norm. -/
def original : ContinuedNeighborhood.Point neighborhood point := classified.1.val.2

/-- Read the SAME retained fine-grid stem with all its ordered occurrences. -/
def originalStem : Walks.Walk retained.grid face.cell.box.anchor point := classified.1.val.1

/-- Read the one actual fine-frame classification of that original Point Owner. -/
def selected : OwnerSelection (retained.localFrames.frameAt point member).owners sample.owner := classified.2.1.val

/-- Read the original face Entry derived for this exact supplied Point Owner. -/
def entry : Entry models point sample.owner := classified.2.2.val

/-- The retained Point is the complete original cache, without reacquisition. -/
theorem original_eq : classified.original = sample := congrArg Prod.snd classified.1.property

/-- The retained stem is the complete original ordered walk. -/
theorem originalStem_eq : classified.originalStem = stem := congrArg Prod.fst classified.1.property

/-- The cached selection is the whole original selector execution on this SAME Point Owner. -/
theorem selected_eq : classified.selected = (retained.localFrames.frameAt point member).select sample.owner :=
  classified.2.1.property

/-- The Entry is its exact named constructor on the same retained selection. -/
theorem entry_eq : classified.entry = retained.entryFromSelection models stem member sample classified.selected :=
  classified.2.2.property

/-- Carry the actual retained Point Entry to its SAME selected fine-frame Owner.

The cached Point-to-frame comparison supplies the erased final
reachability step. The original Entry and selection are consumed directly;
no stem traversal, Point, query, Entry acquisition or comparison is rerun.
-/
def frameEntry : Entry models point
    ((retained.localFrames.frameAt point member).owners classified.selected.index) :=
  ⟨classified.entry.sheet, classified.entry.reached.append
    (Face.Entries.Reached.ofEquivalent classified.selected.equivalent)⟩

/-- The selected frame Entry retains the actual cached Point Entry's old-face sheet. -/
theorem frameEntry_sheet : classified.frameEntry.sheet = classified.entry.sheet := by rfl

/-- The selected signed mesh index reads the whole SAME retained fine-frame Owner.

This uses the original whole-owner vertex readback. The original Point
Owner is a separate owner connected by the cached selection below.
-/
theorem selected_owner_heq (vertices : VertexBank retained.grid) :
    HEq (vertices.owner retained.localFrames (vertices.index point member classified.selected.index))
      ((retained.localFrames.frameAt point member).owners classified.selected.index) :=
  vertices.owner_index_heq retained.localFrames point member classified.selected.index

/-- The actual Point Owner is operationally equivalent to the selected original indexed mesh Owner.

The selection is Point-to-frame. The original vertex-name readback changes
only that SAME frame Owner to its exact indexed representation. This is
signed incidence, with both Owners retained and no geometric filler claim.
-/
def selected_equivalent (vertices : VertexBank retained.grid) :
    NamedEquivalent (ownerName sample.owner)
      (ownerName (vertices.owner retained.localFrames (vertices.index point member classified.selected.index))) :=
  NamedEquivalent.transport rfl
    (vertices.ownerName_index retained.localFrames point member classified.selected.index).symm
    classified.selected.equivalent

/-- The cached Point Entry's sheet is the original reverse-stem target of its retained selection.

Only the whole retained Entry factory is projected. Its original
atVertex_sheet law reads the SAME stem and cached selected index; no
classification, transport row or Point producer is executed.
-/
theorem source_sheet : classified.entry.sheet =
    EdgeBank.RootEdgeBank.target retained.edges stem.reverse classified.selected.index := by
  have actual := congrArg (fun entry : Entry models point sample.owner => entry.sheet) classified.entry_eq
  change classified.entry.sheet = (retained.atVertex models stem member classified.selected.index).sheet at actual
  exact actual.trans (retained.atVertex_sheet models stem member classified.selected.index)

/-- The original forward stem sends this cached old-face sheet to its actual selected Point-frame index.

The same old-anchor reference and retained inverse target maps restore the
selection. No per-fine-vertex reference or desired target relation is an
input, and no root path or observation is acquired.
-/
theorem target_from_sheet : EdgeBank.RootEdgeBank.target retained.edges stem classified.entry.sheet =
    classified.selected.index := by
  let anchor := FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid
  have restored := EdgeBank.RootEdgeBank.target_reverse_right_anchored retained.edges
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop anchor stem classified.selected.index
  exact (congrArg (EdgeBank.RootEdgeBank.target retained.edges stem) classified.source_sheet).trans restored

/-- Any retained Entry on this SAME actual Point chooses the same original face sheet.

This supplies the owned sheet transport used by the original shared
readings operations. It does not equate independent primitive constants.
-/
theorem sheet_eq (known : Entry models point sample.owner) : classified.entry.sheet = known.sheet :=
  classified.entry.sheet_unique known member.inside

end PointEntry

end Point

/-- A SAME support-grid vertex inside the old face is an actual vertex of its retained local cut grid.

Both source-axis occurrences are retained by the original rectangle cut
partition. The whole fine-grid factory then transports only coordinate
membership, never a root-owner or signed-edge relation.
-/
theorem support_vertex {supportAmbient : Geometry.Rational.Box}
    {support : ClearGrid curve.polynomial supportAmbient}
    {partition : Rectangle.Cuts.Partition support face.cell.box}
    {localRows : CellRows old face coarse partition} {point : Canonical}
    (member : FromStates.ContainsVertex support point) (inside : face.cell.box.Contains point) :
    FromStates.ContainsVertex localRows.grid point := by
  have coordinates := partition.vertex_coordinates member inside
  constructor
  · exact Eq.mpr (congrArg (fun values => point.re ∈ values)
      ((congrArg (fun value : ClearGrid curve.polynomial face.cell.box =>
        value.vertical.map ClearGrid.VerticalLine.coordinate) localRows.grid_eq).trans
        (ClearGrid.ofPartition_vertical partition face.clearance))) coordinates.1
  · exact Eq.mpr (congrArg (fun values => point.im ∈ values)
      ((congrArg (fun value : ClearGrid curve.polynomial face.cell.box =>
        value.horizontal.map ClearGrid.HorizontalLine.coordinate) localRows.grid_eq).trans
        (ClearGrid.ofPartition_horizontal partition face.clearance))) coordinates.2

end CellRows

namespace GridCellRows

variable {supportAmbient : Geometry.Rational.Box}
variable {support : ClearGrid curve.polynomial supportAmbient} (rows : GridCellRows old face coarse support)
variable (models : FaceModels frames face) {point : Canonical}
variable (onSupport : FromStates.ContainsVertex support point) (inside : face.cell.box.Contains point)
variable {count : Nat} {neighborhood : ContinuedNeighborhood curve.polynomial count}
variable (sample : ContinuedNeighborhood.Point neighborhood point)

/-- One genuine fine-frame classification retains its once-constructed contained stem and whole old Point.

The support grid, partition, local root rows and Point are original inputs.
Only the pure coordinate connector and one operational classification are
new work; no old query, Point, trace or observation is acquired again.
-/
abbrev PointEntry :=
  let localRows := rows.2
  let anchor := FromStates.ContainsPathVertices.start localRows.grid localRows.boundary.path localRows.boundary_onGrid
  let member := CellRows.support_vertex (localRows := localRows) onSupport inside
  Σ stem : {value : Walks.Walk localRows.grid face.cell.box.anchor point //
      value = LoopMonodromy.Grid.connect localRows.grid face.cell.box.anchor point anchor member},
  localRows.PointEntry models stem.val member sample

/-- Construct actual support-vertex signed incidence in the SAME retained local bank.

The original cut and grid factories derive incidence internally. The
cached Point is classified once, and its resulting Entry supplies the
actual old-face sheet for existing domain/readings transports.
-/
def classifyPoint : rows.PointEntry models onSupport inside sample :=
  let localRows := rows.2
  let anchor := FromStates.ContainsPathVertices.start localRows.grid localRows.boundary.path localRows.boundary_onGrid
  let member := CellRows.support_vertex (localRows := localRows) onSupport inside
  let stem := LoopMonodromy.Grid.connect localRows.grid face.cell.box.anchor point anchor member
  let classified := localRows.classifyPoint models stem member sample
  ⟨⟨stem, rfl⟩, classified⟩

end GridCellRows

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

end
