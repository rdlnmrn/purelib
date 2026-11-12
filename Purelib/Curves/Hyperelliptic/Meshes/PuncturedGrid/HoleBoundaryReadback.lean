module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! The selected face edges form the actual two-lap lifted hole boundary,
with the intermediate root-sheet transports and clockwise order retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleBoundaryReadback
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeListArea)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {hole : Fin base.faces.holes.length}
  {adjacent : HoleAdjacentFaces
    base (base.faces.holes[hole.val]'hole.isLt)}

/-- Start at the hole's lower-left corner, then follow its left, top, right, and bottom inward edges. Each next sheet is
the previous edge's target. -/
def lap (sides : HoleSideLifts lifted adjacent) (sheet : Fin 2) : List (OrientedEdge
  lifted.vertices.count) :=
  let source := (base.faces.holes[hole.val]'hole.isLt)
  let afterLeft := (lifted.edges.edge (source.side .left).reverse).forward.target sheet
  let afterTop := (lifted.edges.edge (source.side .top).reverse).forward.target afterLeft
  let afterRight := (lifted.edges.edge (source.side .right).reverse).forward.target afterTop
  [(sides.left.get sheet).selected.located.lifted.quad.edge .right,
    (sides.top.get afterLeft).selected.located.lifted.quad.edge .bottom,
    (sides.right.get afterTop).selected.located.lifted.quad.edge .left,
    (sides.bottom.get afterRight).selected.located.lifted.quad.edge .top]

/-- The selected adjacent-face lap is exactly the original indexed inward hole boundary. -/
theorem lap_eq (sides : HoleSideLifts lifted adjacent) (sheet : Fin 2) :
    HoleBoundaryReadback.lap sides sheet = lifted.edges.indexedEdges
      lifted.vertices (base.faces.holes[hole.val]'hole.isLt).inwardBoundary sheet := by
  have leftEq := fun sheet => (sides.left.get sheet).edge_eq
  have topEq := fun sheet => (sides.top.get sheet).edge_eq
  have rightEq := fun sheet => (sides.right.get sheet).edge_eq
  have bottomEq := fun sheet => (sides.bottom.get sheet).edge_eq
  simp only [GridSide.opposite, GridSide.kind] at leftEq topEq rightEq bottomEq
  dsimp only [HoleBoundaryReadback.lap]
  rw [leftEq, topEq, rightEq, bottomEq]
  rfl

/-- The two actual inward hole laps in initial-sheet order. -/
def boundaryEdges (sides : HoleSideLifts lifted adjacent) : List (OrientedEdge
  lifted.vertices.count) :=
  HoleBoundaryReadback.lap sides 0 ++
    HoleBoundaryReadback.lap sides 1

/-- The retained adjacent-face edge list is exactly the original lifted hole boundary. -/
theorem boundaryEdges_eq (sides : HoleSideLifts lifted adjacent) :
    HoleBoundaryReadback.boundaryEdges sides =
      (base.faces.holes[hole.val]'hole.isLt).liftedBoundary lifted.vertices lifted.edges := by
  rw [HoleBoundaryReadback.boundaryEdges,
    HoleBoundaryReadback.lap_eq sides,
    HoleBoundaryReadback.lap_eq sides,
    (base.faces.holes[hole.val]'hole.isLt).liftedBoundary_eq]

/-- The complete retained two-lap hole boundary closes at the original sheet-zero anchor. -/
theorem boundaryEdges_closed (sides : HoleSideLifts lifted adjacent) :
    PathEndpoints OrientedEdge.start OrientedEdge.finish
      (HoleBoundaryReadback.boundaryEdges sides)
      (lifted.vertices.index (base.faces.holes[hole.val]'hole.isLt).cell.box.anchor
        ((base.faces.holes[hole.val]'hole.isLt).cell.anchor_mem (base.faces.holes[hole.val]'hole.isLt).member) 0)
      (lifted.vertices.index (base.faces.holes[hole.val]'hole.isLt).cell.box.anchor
        ((base.faces.holes[hole.val]'hole.isLt).cell.anchor_mem (base.faces.holes[hole.val]'hole.isLt).member) 0) := by
  rw [HoleBoundaryReadback.boundaryEdges_eq sides]
  exact (base.faces.holes[hole.val]'hole.isLt).liftedBoundary_closed lifted.vertices lifted.edges

/-- The retained hole boundary area equals the original inward two-sheet area. -/
theorem boundaryEdges_area (sides : HoleSideLifts lifted adjacent)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    Stokes.edgeListArea primitive (HoleBoundaryReadback.boundaryEdges sides) =
      lifted.edges.twoSheetArea lifted.vertices primitive (base.faces.holes[hole.val]'hole.isLt).inwardBoundary := by
  rw [HoleBoundaryReadback.boundaryEdges_eq sides]
  exact (base.faces.holes[hole.val]'hole.isLt).liftedBoundary_area lifted.vertices lifted.edges primitive

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleBoundaryReadback
