module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

/-! # The original four Entry caches at their literal signed quad indices

Only whole-owner index transport is new. Each result consumes the actual
stored corner Entry. No Point, frame selection, row or join is prepared.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Surface.Sewing

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} {retained : CellRows old face coarse cuts}
variable {models : FaceModels frames face} {base : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor base}
variable {member : FromStates.ContainsVertex retained.grid base}
variable {oldCount : Nat} {oldNeighborhood : ContinuedNeighborhood curve.polynomial oldCount}
variable {oldSample : ContinuedNeighborhood.Point oldNeighborhood base}
variable {classified : retained.PointEntry models stem member oldSample}
variable {located : ClearGrid.CornerLocation retained.grid base} {vertices : VertexBank retained.grid}

/-- Move one actual stored Entry to the exact original VertexBank owner readback. -/
private def indexedCorner {point : Canonical} (onGrid : FromStates.ContainsVertex retained.grid point)
    (index : Fin 2) (slot : Fin vertices.count) (same : slot = vertices.index point onGrid index)
    (entry : Entry models point ((retained.localFrames.frameAt point onGrid).owners index)) :
    {value : Entry models (vertices.coordinate slot) (vertices.owner retained.localFrames slot) //
      value.sheet = entry.sheet} := by
  have coordinate := (congrArg vertices.coordinate same).trans (vertices.coordinate_index point onGrid index)
  have owners : HEq (vertices.owner retained.localFrames slot)
      ((retained.localFrames.frameAt point onGrid).owners index) := by
    cases same
    exact vertices.owner_index_heq retained.localFrames point onGrid index
  exact ⟨⟨entry.sheet, entry.reached.castFinish coordinate.symm owners.symm⟩, rfl⟩

variable (lifted : classified.CellLift located vertices)

/-- The original face Entry at one literal signed corner, with its retained sheet law. -/
@[expose] def CornerEntry (corner : Fin 4) : Type :=
  {value : Entry models (vertices.coordinate (lifted.cell.quad.corner corner))
    (vertices.owner retained.localFrames (lifted.cell.quad.corner corner)) //
    value.sheet = classified.entry.sheet}

/-- Read the actual original Entry at any one of the four retained signed corner occurrences.

The complete corner product supplies the data. Original whole-owner
readbacks change only its dependent index; their sheet equation is
composed with the cached product's original old-face sheet law.
-/
def cornerEntry : (corner : Fin 4) → lifted.CornerEntry corner := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))))
  · change lifted.CornerEntry 0
    unfold CornerEntry
    rw [lifted.cell.quad.corner_zero]
    let value := indexedCorner (located.cell.anchor_mem located.member) lifted.source _ lifted.cell.first_eq
      lifted.entries.1
    exact ⟨value.val, value.property.trans lifted.entries_sheets.1⟩
  · change lifted.CornerEntry 1
    unfold CornerEntry
    rw [lifted.cell.quad.corner_one]
    let value := indexedCorner (located.cell.bottomSide located.member).vertices.2
      ((retained.edges.edge (located.cell.bottomSide located.member)).forward.target lifted.source)
      _ lifted.cell.second_eq lifted.entries.2.1
    exact ⟨value.val, value.property.trans lifted.entries_sheets.2.1⟩
  · change lifted.CornerEntry 2
    unfold CornerEntry
    rw [lifted.cell.quad.corner_two]
    let value := indexedCorner (located.cell.rightSide located.member).vertices.2
      ((retained.edges.edge (located.cell.rightSide located.member)).forward.target
        ((retained.edges.edge (located.cell.bottomSide located.member)).forward.target lifted.source))
      _ lifted.cell.third_eq lifted.entries.2.2.1
    exact ⟨value.val, value.property.trans lifted.entries_sheets.2.2.1⟩
  · change lifted.CornerEntry 3
    unfold CornerEntry
    rw [lifted.cell.quad.corner_three]
    let value := indexedCorner (located.cell.topSide located.member).vertices.2
      ((retained.edges.edge (located.cell.topSide located.member)).forward.target
        ((retained.edges.edge (located.cell.rightSide located.member)).forward.target
          ((retained.edges.edge (located.cell.bottomSide located.member)).forward.target lifted.source)))
      _ lifted.cell.fourth_eq lifted.entries.2.2.2
    exact ⟨value.val, value.property.trans lifted.entries_sheets.2.2.2⟩

/-- The actual selected source corner retains its original old-face sheet. -/
theorem cornerEntry_sheet (corner : Fin 4) :
    (lifted.cornerEntry corner).val.sheet = classified.entry.sheet := (lifted.cornerEntry corner).property

/-- Read any original source-face corner from those SAME retained corner Entries.

The source face/corner indices choose the exact quadrilateral occurrence.
This selector preserves reversal and repeated slots, independently of
whether two coordinates happen to be equal.
-/
def sourceEntry (position : Fin 2) (corner : Fin 3) :
    {value : Entry models
        (vertices.coordinate (SewnPrimitiveFaces.corner
          (lifted.cell.quad.faces position) corner))
        (vertices.owner retained.localFrames (SewnPrimitiveFaces.corner
          (lifted.cell.quad.faces position) corner)) //
      value.sheet = classified.entry.sheet} :=
  Eq.mp (congrArg (fun index =>
    {value : Entry models (vertices.coordinate index) (vertices.owner retained.localFrames index) //
      value.sheet = classified.entry.sheet}) (lifted.cell.quad.faceCorner_eq position corner))
    (lifted.cornerEntry
      (IndexedQuadrilateral.faceCorner position corner))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
