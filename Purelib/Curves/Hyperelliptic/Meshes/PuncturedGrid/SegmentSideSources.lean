module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Topology.Mesh.QuadrilateralDual

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Identify rectangle-side sources on the original retained segment routes.
Axis-parallel grid segments cannot select a rectangle diagonal. The source
triangle, sheet, orientation and occurrence order are retained exactly. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge (Kind)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}

/-- Two Gaussian endpoints share their real or imaginary coordinate. -/
def AxisAligned (first last : Data.Gaussian.Basic.Canonical) : Prop := first.re = last.re ∨ first.im = last.im

/-- Axis alignment is preserved when the actual endpoints are exchanged. -/
theorem AxisAligned.symm {first last : Data.Gaussian.Basic.Canonical} (aligned :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned first last) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned last first :=
  aligned.elim (fun same => Or.inl same.symm) (fun same => Or.inr same.symm)

/-- Every retained clear grid segment is axis aligned. -/
theorem segment_axisAligned {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned start finish := by
  cases segment with
  | horizontal => exact Or.inr rfl
  | vertical => exact Or.inl rfl

/-- The diagonal of a proper retained rectangular face is not axis aligned. -/
public theorem diagonal_not_aligned {face : PuncturedGridFaces.RegularFace bank} {sheet : Fin 2}
    (lifted : BranchCellBank.LiftedFace vertices edges face sheet) :
    ¬AxisAligned (vertices.coordinate lifted.quad.first) (vertices.coordinate lifted.quad.third) := by
  rw [lifted.coordinates.1, lifted.coordinates.2.2.1]
  intro aligned
  exact aligned.elim (fun same => (ne_of_lt face.cell.box_proper.1) same)
    (fun same => (ne_of_lt face.cell.box_proper.2) same)

namespace LiftedFaces.EdgeLocation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedFaces.EdgeLocation in
/-- Identify the retained rectangle side of an axis-aligned edge location; properness excludes both diagonals. -/
def side {edge : Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge)
    (aligned : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned (vertices.coordinate edge.start)
      (vertices.coordinate edge.finish)) :
    { side : GridLiftedDualSteps.GridSide // side.kind = location.kind } := by
  have coordinates : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned (vertices.coordinate
    (location.lifted.quad.edge location.kind).start)
      (vertices.coordinate (location.lifted.quad.edge location.kind).finish) := location.edge_eq.symm ▸ aligned
  cases equal : location.kind with
  | bottom => exact ⟨.bottom, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | top => exact ⟨.top, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | upDiagonal =>
      rw [equal] at coordinates
      exact False.elim (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.diagonal_not_aligned
        location.lifted coordinates)
  | downDiagonal =>
      rw [equal] at coordinates
      exact False.elim (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.diagonal_not_aligned
        location.lifted coordinates.symm)

end LiftedFaces.EdgeLocation

namespace LiftedMesh

set_option genInjectivity false in
/-- One retained oriented side occurrence in the original lifted regular mesh.

The position and sheet identify its actual face, and the direction flag determines the original source-edge orientation.
-/
structure SideOccurrence (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) where
  /-- The original regular-face position of this occurrence. -/ position : Fin faces.regulars.length
  /-- The retained root sheet of the located face. -/ sheet : Fin 2
  /-- The actual rectangle side selected by this occurrence. -/ side : GridLiftedDualSteps.GridSide
  /-- Whether this occurrence traverses the original side source backward. -/ backward : Bool

constructive_injectivity SideOccurrence

namespace SideOccurrence

/-- The original triangle source of the retained side occurrence, reversed exactly when requested. -/
def source (occurrence : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence mesh) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  let forward : SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
    ⟨mesh.triangleIndex occurrence.position occurrence.sheet (QuadOccurrence.upperSide occurrence.side.kind),
      FaceCorners.firstCorner occurrence.side.kind, FaceCorners.lastCorner occurrence.side.kind⟩
  if occurrence.backward then ⟨forward.source, forward.last, forward.first⟩ else forward

end SideOccurrence

namespace EdgeRoute

variable {edge : Purelib.Topology.Polygon.Stokes.OrientedEdge vertices.count}

/-- Read the original oriented side occurrence of an axis-aligned retained edge route, with exact source-edge equality.
-/
def sideOccurrence (route : MeshPathWalks.EdgeRoute mesh edge)
    (aligned : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.AxisAligned (vertices.coordinate edge.start)
      (vertices.coordinate edge.finish)) :
    { occurrence : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence mesh //
      occurrence.source = route.sourceEdge } := by
  cases route with
  | forward location =>
      let selected := Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedFaces.EdgeLocation.side
        location aligned
      refine ⟨⟨location.position, location.sheet, selected.val, false⟩, ?_⟩
      change (⟨_, FaceCorners.firstCorner selected.val.kind, FaceCorners.lastCorner selected.val.kind⟩ :
        SewnPrimitiveContacts.SourceEdge _) = _
      rw [selected.property]
      rfl
  | backward location =>
      let selected := Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedFaces.EdgeLocation.side
        location aligned.symm
      refine ⟨⟨location.position, location.sheet, selected.val, true⟩, ?_⟩
      change (⟨_, FaceCorners.lastCorner selected.val.kind, FaceCorners.firstCorner selected.val.kind⟩ :
        SewnPrimitiveContacts.SourceEdge _) = _
      rw [selected.property]
      rfl

end EdgeRoute

namespace SegmentFace
variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}

/-- Read the actual oriented side occurrence of the original retained grid-segment placement. -/
def sideOccurrence (placement : LiftedMesh.SegmentFace mesh segment) :
    { occurrence : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence mesh //
      occurrence.source = placement.location.sourceEdge } :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.EdgeRoute.sideOccurrence placement.location
    (by
        rw [placement.start_eq, placement.finish_eq];
        exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.segment_axisAligned segment)

end SegmentFace
end LiftedMesh
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
