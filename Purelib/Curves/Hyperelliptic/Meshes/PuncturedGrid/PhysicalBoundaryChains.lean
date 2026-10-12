module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
public import Purelib.Topology.Surface.Sewing.AreaChainTests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Actual oriented chain identity for the physical boundary

The existing closed boundary tours, including both laps at each branch,
represent the mesh boundary for arbitrary antisymmetric edge values. The
finite test argument discharges this from the proved primitive-area identity;
no boundary matching or successful checker is supplied by the caller.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge (map)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)

/-- Finite summation of primitive areas equals primitive-area evaluation on the concatenated original edge words. -/
private theorem area_flatten {count : Nat} (points : Fin count → Stokes.PrimitivePoint)
    (words : List (List (Stokes.OrientedEdge count))) :
    Stokes.edgeListArea points words.flatten = CellBoundary.sumValues (Stokes.edgeListArea points) words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      rw [List.flatten_cons, Stokes.edgeListArea_append, ih]
      rfl

/-- Finite summation of edge-word values equals evaluation on their original concatenation. -/
private theorem value_flatten {count : Nat} (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
    (words : List (List (Stokes.OrientedEdge count))) :
    wordValue value words.flatten = CellBoundary.sumValues (wordValue value) words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      rw [List.flatten_cons, wordValue_append, ih]
      rfl

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- Every antisymmetric edge value agrees on the actual mesh boundary and the original flattened physical boundary
tours. -/
theorem boundary_chain_eq (lifted : Meshes.LiftedPuncturedGrid base)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    wordValue value lifted.mesh.triangulation.boundary = wordValue value lifted.boundaryLoops.flatten :=
  AreaChainTests.wordValue_eq (fun points =>
    (lifted.boundary_eq_closedLoops points).trans
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.area_flatten points lifted.boundaryLoops).symm)
      value anti

/-- Every antisymmetric edge value on the actual mesh boundary is the sum over the retained original physical boundary
tours. -/
theorem boundary_chain_eq_loops (lifted : Meshes.LiftedPuncturedGrid base)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    wordValue value lifted.mesh.triangulation.boundary = CellBoundary.sumValues (wordValue value) lifted.boundaryLoops
      :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.boundary_chain_eq lifted value anti).trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.value_flatten value lifted.boundaryLoops)

/-- Exact signed multiplicities on the original sheet-labelled vertices. This is an incidence certificate, not an
equality of boundary areas at just one primitive sample and not an assertion of equal raw list lengths. -/
theorem boundary_coefficients (lifted : Meshes.LiftedPuncturedGrid base)
    (selected : Stokes.OrientedEdge lifted.vertices.count) :
    AreaChainTests.coefficient selected lifted.mesh.triangulation.boundary =
      AreaChainTests.coefficient selected lifted.boundaryLoops.flatten :=
  AreaChainTests.coefficient_eq (fun points =>
    (lifted.boundary_eq_closedLoops points).trans
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.area_flatten points lifted.boundaryLoops).symm)
      selected

/-- A positively oriented physical boundary coefficient occurs exactly where the actual mesh has an edge but no reverse
occurrence. No simplicity or disjoint-component assumption about the displayed tours is used. -/
theorem boundary_coefficient_one_iff (lifted : Meshes.LiftedPuncturedGrid base)
    (selected : Stokes.OrientedEdge lifted.vertices.count) :
    AreaChainTests.coefficient selected lifted.boundaryLoops.flatten = 1 ↔
      selected ∈ Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces ∧
        selected.reverse ∉ Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces := by
  rw [← Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.boundary_coefficients lifted selected,
    ← AreaChainTests.triangulation_coefficient]
  exact AreaChainTests.coefficient_eq_one_iff selected _ lifted.mesh.orientedEdges_unique

/-- The residual boundary of the actual cut polygon has precisely the positive oriented support of the physical closed
tours. -/
theorem cut_boundary_iff_physical_coefficient (lifted : Meshes.LiftedPuncturedGrid base)
    (selected : Stokes.OrientedEdge lifted.vertices.count) :
    selected ∈ lifted.cutBoundaryPairs.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
      AreaChainTests.coefficient selected lifted.boundaryLoops.flatten = 1 :=
  (lifted.cutBoundaryPairs_boundary_iff selected).trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains.boundary_coefficient_one_iff lifted selected).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains
