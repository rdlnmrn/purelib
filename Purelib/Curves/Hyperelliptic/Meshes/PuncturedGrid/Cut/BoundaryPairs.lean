module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Topology.Surface.Cut.BoundaryPairs
public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Data.List

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Actual lifted cut boundaries with complete occurrence pairing

The geometric grid proves nondegenerate surface edges, so its cut polygon
admits the total projected pairing without any extra input. The residual
occurrences are exactly the one-sided mesh boundary. Paired occurrences keep
separate cut vertices, ready for primitive jumps and subsequent A/B reduction.
-/

section

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)

namespace Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

/-- Every oriented triangle edge of a proper coordinate rectangle has distinct retained vertex indices. -/
theorem edges_nonloop {count : Nat} {coordinate : Fin count → Data.Gaussian.Basic.Canonical}
    {box : Rational.Box} {quad : IndexedQuadrilaterals.IndexedQuadrilateral count}
    (geometry : IndexedQuadrilateral.RectangleCoordinates quad coordinate box) (proper : box.Proper)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ quad.triangles.flatMap OrientedTriangle.boundary) :
    edge.start ≠ edge.finish := by
  rw [IndexedQuadrilateral.triangleEdges_eq quad] at member
  obtain ⟨kind, _, same⟩ := Map.mem_map.mp member
  cases same
  intro equal
  have coordinates := geometry.edge_coordinates kind
  have first := congrArg Prod.fst coordinates
  have last := congrArg Prod.snd coordinates
  have ends := first.symm.trans ((congrArg coordinate equal).trans last)
  have x := congrArg Data.Gaussian.Basic.re ends
  have y := congrArg Data.Gaussian.Basic.im ends
  cases kind <;> first
    | exact (ne_of_lt proper.1) x
    | exact (ne_of_lt proper.1) x.symm
    | exact (ne_of_lt proper.2) y
    | exact (ne_of_lt proper.2) y.symm

end Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

end

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh

/-- Every edge occurrence of the actual lifted triangulation has distinct original vertex-bank endpoints. -/
theorem orientedEdges_nonloop
    {bank : Branches.BranchCellBank curve branches higher} {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames} {faces :
      PuncturedGridFaces.PuncturedFaces bank}
    (mesh : GridLiftedMesh.LiftedMesh vertices edges faces)
    (edge : Stokes.OrientedEdge vertices.count) (member : edge ∈ Stokes.triangleEdgeOccurrences
      mesh.triangulation.faces) :
    edge.start ≠ edge.finish := by
  rw [mesh.triangleEdges_eq] at member
  obtain ⟨face, _, sheet, lifted, member⟩ := mesh.lifts.triangleEdge_member member
  exact lifted.rectangleCoordinates.edges_nonloop face.cell.box_proper member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

section

variable {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The actual canonical polygon now carries a complete, occurrence-sensitive pairing, with both finite construction
obligations discharged geometrically. -/
def cutBoundaryPairs (lifted : Meshes.LiftedPuncturedGrid base) :
    ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary :=
  SinglePolygon.edgePairing lifted.cutPolygon

      (BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      lifted.mesh)

/-- The retained unpaired cut occurrences are exactly the original triangulation edges whose reverse does not occur. -/
theorem cutBoundaryPairs_boundary_iff (lifted :
  Meshes.LiftedPuncturedGrid base)
    (edge : Stokes.OrientedEdge lifted.vertices.count) :
    edge ∈ lifted.cutBoundaryPairs.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
      edge ∈ Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces ∧
        edge.reverse ∉ Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces :=
  SinglePolygon.boundary_iff lifted.cutPolygon
    lifted.mesh.orientedEdges_unique lifted.cutBoundaryPairs edge

/-- Materialize all jump and defect calculations on the actual cut polygon. No primitive descent to the original vertex
bank is required. -/
def cutBoundarySample (lifted : Meshes.LiftedPuncturedGrid base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint) :
    ProjectedEdgePairing.PrimitiveSample lifted.cutBoundaryPairs primitive :=
  PrimitiveSample.build lifted.cutBoundaryPairs primitive

/-- The actual cut-triangle primitive area is the retained boundary area plus the paired jump and defect sums. -/
theorem cutSurface_eq_boundary_jumps_defects (lifted :
  Meshes.LiftedPuncturedGrid base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint)
    (sample : ProjectedEdgePairing.PrimitiveSample lifted.cutBoundaryPairs primitive) :
    Stokes.edgeListArea primitive (lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      sample.boundaryArea + sample.jumpSum + sample.defectSum :=
  (lifted.cutPolygon.patch.cut.boundary_area primitive).symm.trans sample.boundary_decomposition

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end

end
