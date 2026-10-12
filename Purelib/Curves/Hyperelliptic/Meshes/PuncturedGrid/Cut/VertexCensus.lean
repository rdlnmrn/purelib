module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Nodup
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Data.List.Permutation
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.VertexGluing
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.BoundaryVertices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexGluing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Actual cut vertices, projected fibers, and paired-cut counts

The boundary sources enumerate every active cut vertex once. Their actual
surface labels are a complete, exact set of gluing fibers. Physical edges
are counted using the certified disjoint boundary cycles, rather than raw
allocation counts or signed-chain multiplicities alone.
-/

section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryPairs
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest
open Purelib.Topology.Surface.Cut.BoundaryVertices.CutPatch
open Purelib.Topology.Surface.Cut.BoundaryVertices.SewingForest
open Purelib.Topology.Surface.Cut.VertexGluing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)
open Purelib.Topology.Surface.Cut.VertexGluing (PairVertexJoin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus

set_option genInjectivity false in
/-- Retain the cut-vertex enumeration and its actual surface-label fibers.

The cached boundary-start list enumerates each active cut vertex once. Its
retained fibers agree exactly with the endpoint identifications of actual pairs. -/
structure CutVertexCensus (lifted : Meshes.LiftedPuncturedGrid base) where
  /-- The cached original boundary-source vertices of the retained cut polygon. -/ vertices : List (Fin
    lifted.cutPolygon.patch.cut.count)
  /-- The cached vertices are exactly the start labels of the original cut boundary. -/ vertices_eq : vertices =
    lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start
  /-- The retained original cut-vertex enumeration has no duplicates. -/ unique : vertices.Nodup
  /-- The retained enumeration contains exactly the original active cut vertices. -/ active_iff : ∀ vertex, vertex ∈
    vertices ↔
    CutPatch.ActiveVertex lifted.cutPolygon.patch.cut vertex
  /-- The actual finite active-vertex certificate of the original lifted mesh. -/ fibers : ActiveVertices
    lifted.mesh
  /-- The retained surface vertices are exactly the images of the original cut-vertex enumeration. -/ fiber_iff : ∀
    vertex, vertex ∈ fibers.indices ↔
    vertex ∈ vertices.map lifted.cutPolygon.patch.cut.vertexLabels
  /-- Actual paired-cut endpoint identifications agree exactly with equality of the original surface labels. -/
    joined_iff : ∀ first ∈ vertices, ∀ last ∈ vertices,
    VertexGluing.PairVertexJoin lifted.cutBoundaryPairs.pairs first last ↔
      lifted.cutPolygon.patch.cut.vertexLabels first = lifted.cutPolygon.patch.cut.vertexLabels last

constructive_injectivity CutVertexCensus

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- Cache the actual original cut vertices and exact surface-label fibers of the retained paired-cut identifications. -/
@[expose] def cutVertexCensus (lifted : Meshes.LiftedPuncturedGrid
  base) : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus.CutVertexCensus lifted where
  vertices := lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start
  vertices_eq := rfl
  unique := lifted.cutPolygon.patch.cut.simple
  active_iff := fun vertex =>
    (Assembly.active_iff_boundary
      lifted.cutPolygon.patch.assembly vertex).symm
  fibers := LiftedMesh.activeVertices lifted.mesh
  fiber_iff := fun vertex => ((LiftedMesh.activeVertices lifted.mesh).active_iff vertex).trans
    (SinglePolygon.boundary_projection_mem_iff
      lifted.cutPolygon vertex).symm
  joined_iff := fun first firstMember last lastMember =>
    VertexGluing.cutVertexJoin_iff lifted
      ((Assembly.active_iff_boundary
        lifted.cutPolygon.patch.assembly first).mpr firstMember)
      ((Assembly.active_iff_boundary
        lifted.cutPolygon.patch.assembly last).mpr lastMember)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus.CutVertexCensus

/-- The original cut boundary has exactly two more retained vertices than lifted triangles. -/
theorem vertices_length {lifted : Meshes.LiftedPuncturedGrid base} (census :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus.CutVertexCensus lifted) :
    census.vertices.length = lifted.mesh.triangles.length + 2 := by
  rw [census.vertices_eq, Data.List.Map.length_map]
  exact lifted.cutPolygon.boundaryCount

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus.CutVertexCensus

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus

/-- Every original paired cut contributes exactly two retained edge occurrences. -/
private theorem paired_occurrences_length {source target : Nat} {labels : Fin source → Fin target}
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) : (ProjectedEdgePair.occurrences pairs).length = 2 *
      pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => change _ + 1 + 1 = _; rw [ih, List.length_cons]; omega

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The original unpaired cut-edge count equals the exact total length of retained physical boundary components. -/
theorem cutBoundaryPairs_physical_length (lifted :
  Meshes.LiftedPuncturedGrid base) :
    lifted.cutBoundaryPairs.boundary.length = lifted.boundaryComponents.cycles.flatten.length := by
  have cutUnique : (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map
    lifted.cutPolygon.patch.cut.vertexLabels)).Nodup := by
    rw [lifted.cutPolygon.patch.cut.boundary_eq]
    exact SewnPatch.boundary_unique lifted.cutPolygon.patch
      (SinglePolygon.originalEdges_unique lifted.cutPolygon lifted.mesh.orientedEdges_unique)
  have ordering := EdgeReordering.map lifted.cutPolygon.patch.cut.vertexLabels lifted.cutBoundaryPairs.incidence
  rw [Data.List.Map.map_append] at ordering
  have unique := (Permutation.nodup_append_parts
    (Permutation.nodup (EdgeReordering.toPerm ordering) cutUnique)).1
  have forward := Nodup.nodup_length_le_of_mem unique lifted.boundaryComponents.edges_unique
    (fun edge member => (lifted.cut_boundary_iff_boundaryComponents edge).mp member)
  have backward := Nodup.nodup_length_le_of_mem lifted.boundaryComponents.edges_unique unique
    (fun edge member => (lifted.cut_boundary_iff_boundaryComponents edge).mpr member)
  rw [Data.List.Map.length_map] at forward backward
  omega

/-- Every cut-polygon occurrence is either a physical edge or one of the two occurrences of an actual paired cut. -/
theorem cut_pairs_count (lifted : Meshes.LiftedPuncturedGrid base) :
    2 * lifted.cutBoundaryPairs.pairs.length + lifted.boundaryComponents.cycles.flatten.length =
      lifted.mesh.triangles.length + 2 := by
  have count := Permutation.length_eq (EdgeReordering.toPerm lifted.cutBoundaryPairs.incidence)
  rw [Data.List.Append.length_append,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus.paired_occurrences_length,
    lifted.cutBoundaryPairs_physical_length,
    lifted.cutPolygon.boundaryCount] at count
  omega

/-- Count the three directed triangle sides against the actual unoriented edge bank. Interior edges occur twice, and
each exposed edge once. -/
theorem triangle_edge_census (lifted : Meshes.LiftedPuncturedGrid
  base) :
    3 * lifted.mesh.triangles.length + lifted.boundaryComponents.cycles.flatten.length =
      2 * lifted.mesh.surfaceEdges.representatives.length := by
  have partition := base.faces.regulars_degree
  rw [Polynomial.Geometry.Grid.WindowSize.cells_length base.bank.grid] at partition
  have exteriorCount : base.bank.exterior.edgeCount =
      2 * (base.bank.grid.xIntervals.length + base.bank.grid.yIntervals.length) :=
    base.bank.frame.boundary_edgeCount
  change 3 * lifted.mesh.triangles.length + lifted.boundaryLoops.flatten.length = _
  rw [lifted.mesh.surfaceEdges.length_eq, lifted.boundaryLoops_edgeCount, exteriorCount,
    lifted.faceCount, base.bank.frame.horizontal_length, base.bank.frame.vertical_length]
  calc
    _ = 12 * base.faces.regulars.length + 4 * (base.bank.grid.xIntervals.length + base.bank.grid.yIntervals.length) +
        8 * curve.polynomial.natDegree := by ring1
    _ = 8 * (base.bank.grid.xIntervals.length * base.bank.grid.yIntervals.length) +
        4 * (base.bank.grid.xIntervals.length + base.bank.grid.yIntervals.length) + 4 * base.faces.regulars.length := by
          omega
    _ = _ := by ring1

/-- The number of paired cuts is tied to the actual vertex fibers and physical components. Comparing terminal
cancellations to these fibers is the remaining step in identifying the computed handle count. -/
theorem cut_pairs_euler_balance (lifted : Meshes.LiftedPuncturedGrid
  base) :
    (lifted.cutBoundaryPairs.pairs.length : Int) =
      ((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.boundaryComponents.cycles.flatten.length +
        lifted.boundaryComponents.cycles.length + 2 * genus - 1 := by
  have sides := congrArg (fun value : Nat => (value : Int)) lifted.triangle_edge_census
  have cuts := congrArg (fun value : Nat => (value : Int)) lifted.cut_pairs_count
  simp only [Int.natCast_add, Int.natCast_mul, Nat.cast_ofNat] at sides cuts
  have euler := lifted.euler_add_boundaryComponents
  omega

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end

end
