module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.Triangles
public import Purelib.Polynomial.Geometry.Grid.CellCorners
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromPartition
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.SquareRoot.Grid.Walk

/-! # The SAME retained Point at any actual local-cell corner

A whole finite incidence selection retains its ordered corner prefix.
Inverse cached target maps carry the original Point Entry to the cell
anchor, and the SAME rows lift all four corner occurrences. Geometry only
selects the corner; the cached selection and actual rows supply the sign.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} (retained : CellRows old face coarse cuts)

/-- Select an actual fine-cell corner from this SAME retained cut grid's proper endpoints.

The whole grid factory supplies all four axis bounds. The original
Cartesian list is materialized once by locateCorner; Point, query, frame,
root-row and observation acquisition are not part of this selection.
-/
def locateCorner {point : Canonical} (member : FromStates.ContainsVertex retained.grid point) :
    ClearGrid.CornerLocation retained.grid point :=
  ClearGrid.locateCorner retained.grid face.cell.box_proper
    (ClearGrid.ofPartition_bounds_of_eq cuts face.clearance retained.grid_eq) point member

namespace PointEntry

variable {retained} {models : FaceModels frames face} {point : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor point}
variable {member : FromStates.ContainsVertex retained.grid point}
variable {count : Nat} {neighborhood : ContinuedNeighborhood curve.polynomial count}
variable {sample : ContinuedNeighborhood.Point neighborhood point}
variable (classified : retained.PointEntry models stem member sample)
variable (located : ClearGrid.CornerLocation retained.grid point) (vertices : VertexBank retained.grid)

/-- Retain old Point/incidence caches, both ordered prefix directions, source sheet and actual cell lift.

Only pure metadata and derived Entries are new. Each path, source index
and Entry has its original factory equality. The four-corner lift and
entry product use the SAME source sheet and nominal cell/row parents.
-/
abbrev CellLift :=
  {value : retained.PointEntry models stem member sample × ClearGrid.CornerLocation retained.grid point //
    value = (classified, located)} ×
  (Σ paths : {value : Walks.Walk retained.grid located.cell.box.anchor point ×
      Walks.Walk retained.grid point located.cell.box.anchor //
    value.1 = located.walk.2.castEndpoints rfl located.walk_point ∧ value.2 = value.1.reverse},
  Σ source : {value : Fin 2 //
    value = EdgeBank.RootEdgeBank.target retained.edges paths.val.2 classified.selected.index},
  Σ first : {value : Entry models located.cell.box.anchor
      ((retained.localFrames.frameAt _ (located.cell.anchor_mem located.member)).owners source.val) //
    value = Entry.castIndex (retained.localFrames.frameAt _ (located.cell.anchor_mem located.member))
      source.property.symm
      (Entry.followWalk (models := models) retained.edges paths.val.2 member
        (located.cell.anchor_mem located.member)
        (InBox.ofWithin paths.val.2.path paths.val.2.withinAmbient member.inside)
        classified.selected.index classified.frameEntry)},
  retained.LiftedCell vertices located.cell located.member source.val ×
    {value : retained.CornerEntries located.cell located.member source.val models //
      value = retained.cornerEntries located.cell located.member source.val models first.val})

/-- Lift the SAME actual Point at the selected one of all four fine-cell corners.

The reverse prefix reads the actual cached inverse targets. The existing
Point Entry and selection propagate backward through those same rows;
no Owner is chosen from coordinates and no Point/row bank is duplicated.
-/
def liftAtCorner : classified.CellLift located vertices :=
  let path := located.walk.2.castEndpoints rfl located.walk_point
  let reverse := path.reverse
  let source := EdgeBank.RootEdgeBank.target retained.edges reverse classified.selected.index
  let arrived := Entry.followWalk (models := models) retained.edges reverse member
    (located.cell.anchor_mem located.member)
    (InBox.ofWithin reverse.path reverse.withinAmbient member.inside)
    classified.selected.index classified.frameEntry
  let first := Entry.castIndex (retained.localFrames.frameAt _ (located.cell.anchor_mem located.member)) rfl arrived
  let lifted := retained.liftCell vertices located.cell located.member source
  let entries := retained.cornerEntries located.cell located.member source models first
  (⟨(classified, located), rfl⟩,
    ⟨⟨(path, reverse), rfl, rfl⟩, ⟨source, rfl⟩, ⟨first, rfl⟩, lifted, ⟨entries, rfl⟩⟩)

namespace CellLift

variable {classified located vertices} (lifted : classified.CellLift located vertices)

/-- Read the whole original cached Point classification. -/
def original : retained.PointEntry models stem member sample := lifted.1.val.1

/-- Read the whole original finite incidence selection, including its one cell-list value. -/
def location : ClearGrid.CornerLocation retained.grid point := lifted.1.val.2

/-- Read the actual selected corner from the retained incidence cache. -/
def corner : Fin 4 := lifted.location.corner

/-- Read the SAME cached oriented prefix from cell anchor to this actual Point. -/
def path : Walks.Walk retained.grid located.cell.box.anchor point := lifted.2.1.val.1

/-- Read the SAME cached reversed prefix, preserving all original occurrences. -/
def reverse : Walks.Walk retained.grid point located.cell.box.anchor := lifted.2.1.val.2

/-- Read the once-computed actual reverse-target sheet at the cell anchor. -/
def source : Fin 2 := lifted.2.2.1.val

/-- Read the original Point Entry propagated along the actual reverse rows. -/
def first : Entry models located.cell.box.anchor
    ((retained.localFrames.frameAt _ (located.cell.anchor_mem located.member)).owners lifted.source) :=
  lifted.2.2.2.1.val

/-- Read all four retained signed quadrilateral occurrences, not a new factory execution. -/
def cell : retained.LiftedCell vertices located.cell located.member lifted.source := lifted.2.2.2.2.1

/-- Read the four original face Entries on those SAME ordered corner-frame Owners. -/
def entries : retained.CornerEntries located.cell located.member lifted.source models := lifted.2.2.2.2.2.val

/-- The complete original Point cache is retained unchanged. -/
theorem original_eq : lifted.original = classified := congrArg Prod.fst lifted.1.property

/-- The complete finite incidence cache is retained unchanged. -/
theorem location_eq : lifted.location = located := congrArg Prod.snd lifted.1.property

/-- The retained corner is the whole original incidence choice. -/
theorem corner_eq : lifted.corner = located.corner := congrArg ClearGrid.CornerLocation.corner lifted.location_eq

/-- The path is the SAME retained geometric prefix with only its certified endpoint reindexed. -/
theorem path_eq : lifted.path = located.walk.2.castEndpoints rfl located.walk_point := lifted.2.1.property.1

/-- The complete cached reverse is the original reversal of that SAME prefix. -/
theorem reverse_eq : lifted.reverse = lifted.path.reverse := lifted.2.1.property.2

/-- The cached source sheet is the original reverse target of the cached Point selection. -/
theorem source_eq : lifted.source = EdgeBank.RootEdgeBank.target retained.edges lifted.reverse
    classified.selected.index := lifted.2.2.1.property

/-- Forward traversal of that SAME prefix restores the actual selected Point-frame index. -/
theorem restored : EdgeBank.RootEdgeBank.target retained.edges lifted.path lifted.source =
    classified.selected.index := by
  have reference := (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
    (face.cell.anchor_mem face.member)).toLoop
  have anchor := FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid
  have inverse := EdgeBank.RootEdgeBank.target_reverse_right_anchored retained.edges reference anchor lifted.path
    classified.selected.index
  exact (congrArg (EdgeBank.RootEdgeBank.target retained.edges lifted.path) lifted.source_eq).trans
    ((congrArg (fun reverse => EdgeBank.RootEdgeBank.target retained.edges lifted.path
      (EdgeBank.RootEdgeBank.target retained.edges reverse classified.selected.index)) lifted.reverse_eq).trans inverse)

/-- Whole equal prefix results give equal endpoint-reindexed copies of those SAME walks. -/
private theorem prefixPath_eq {first : Canonical}
    {before after : (finish : Canonical) × Walks.Walk retained.grid first finish}
    (same : before = after) (beforePoint : before.1 = point) (afterPoint : after.1 = point) :
    before.2.castEndpoints rfl beforePoint = after.2.castEndpoints rfl afterPoint := by
  cases same
  rfl

/-- The selected signed quadrilateral corner is the exact original Point-frame index. -/
private theorem corner_index_original : lifted.cell.quad.corner located.corner =
    vertices.index point member classified.selected.index := by
  have rawPoint := (located.cell.cornerPrefix_point located.member located.corner).trans located.point_eq.symm
  have raw := lifted.cell.corner_index_at located.corner rawPoint member
  have path : lifted.path = (located.cell.cornerPrefix located.member located.corner).2.castEndpoints rfl rawPoint :=
    lifted.path_eq.trans (prefixPath_eq located.walk_eq located.walk_point rawPoint)
  exact raw.trans ((congrArg (fun path => vertices.index point member
    (EdgeBank.RootEdgeBank.target retained.edges path lifted.source)) path.symm).trans
      (congrArg (vertices.index point member) lifted.restored))

/-- The actual retained corner has the actual cached Point selection's signed index. -/
theorem corner_index : lifted.cell.quad.corner lifted.corner =
    vertices.index point member lifted.original.selected.index :=
  (congrArg (fun corner => lifted.cell.quad.corner corner) lifted.corner_eq).trans
    (lifted.corner_index_original.trans
      (congrArg (vertices.index point member)
        (congrArg (fun original => original.selected.index) lifted.original_eq).symm))

/-- Compare the SAME actual Point Owner to its exact retained signed triangle-corner Owner.

The inverse row maps identify its index. Only the cached Point-to-frame
selection supplies the signed comparison; geometric incidence alone does
not identify root Owners and no observed join is acquired here.
-/
def cornerEquivalent : NamedEquivalent (ownerName sample.owner)
    (ownerName (vertices.owner retained.localFrames (lifted.cell.quad.corner lifted.corner))) :=
  NamedEquivalent.transport rfl
    (congrArg (fun index => ownerName (vertices.owner retained.localFrames index)) lifted.corner_index).symm
    (lifted.original.selected_equivalent vertices)

/-- The backward Entry is its actual whole original row-following constructor on the cached Point Entry. -/
theorem first_eq : lifted.first =
    Entry.castIndex (retained.localFrames.frameAt _ (located.cell.anchor_mem located.member)) lifted.source_eq.symm
      (Entry.followWalk (models := models) retained.edges lifted.reverse member
        (located.cell.anchor_mem located.member)
        (InBox.ofWithin lifted.reverse.path lifted.reverse.withinAmbient member.inside)
        classified.selected.index classified.frameEntry) := lifted.2.2.2.1.property

/-- The actual anchor Entry retains the SAME cached Point Entry's original old-face sheet. -/
theorem first_sheet : lifted.first.sheet = classified.entry.sheet :=
  (congrArg Entry.sheet lifted.first_eq).trans
    ((Entry.castIndex_sheet (retained.localFrames.frameAt _ (located.cell.anchor_mem located.member))
      lifted.source_eq.symm _).trans
        ((Entry.followWalk_sheet (models := models) retained.edges lifted.reverse member
          (located.cell.anchor_mem located.member)
          (InBox.ofWithin lifted.reverse.path lifted.reverse.withinAmbient member.inside)
          classified.selected.index classified.frameEntry).trans classified.frameEntry_sheet))

/-- The complete four-corner Entry product is its SAME original constructor on the retained first Entry. -/
theorem entries_eq : lifted.entries = retained.cornerEntries located.cell located.member lifted.source models
    lifted.first := lifted.2.2.2.2.2.property

/-- All four actual old-face corner Entries preserve the cached Point Entry's original sheet. -/
theorem entries_sheets : lifted.entries.1.sheet = classified.entry.sheet ∧
    lifted.entries.2.1.sheet = classified.entry.sheet ∧ lifted.entries.2.2.1.sheet = classified.entry.sheet ∧
      lifted.entries.2.2.2.sheet = classified.entry.sheet := by
  rw [lifted.entries_eq]
  have first := congrArg Entry.sheet
    (retained.cornerEntries_first located.cell located.member lifted.source models lifted.first)
  have others := retained.corner_sheets located.cell located.member lifted.source models lifted.first
  exact ⟨first.trans lifted.first_sheet,
    others.1.symm.trans (first.trans lifted.first_sheet),
    others.2.1.symm.trans (first.trans lifted.first_sheet),
    others.2.2.symm.trans (first.trans lifted.first_sheet)⟩

end CellLift

/-- Select a genuine corner once and propagate the SAME retained Point through its original rows.

The first subtype retains the whole cell-list/search/choice/prefix result.
The second retains the complete signed corner lift on that SAME incidence
value. This new finite metadata work performs no Point or root acquisition.
-/
def liftAtVertex :
    Σ located : {value : ClearGrid.CornerLocation retained.grid point // value = retained.locateCorner member},
    {value : classified.CellLift located.val vertices // value = classified.liftAtCorner located.val vertices} :=
  let located := retained.locateCorner member
  let lifted := classified.liftAtCorner located vertices
  ⟨⟨located, rfl⟩, ⟨lifted, rfl⟩⟩

end PointEntry

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

end
