module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Meshes.PuncturedGridFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Topology.Surface.Sewing.AreaChainTests
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Polynomial.Geometry.Grid.Boundary.Simplicity
public import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Disjoint physical boundary cycles of the actual lifted mesh

The displayed root-closed exterior and hole tours have globally distinct
source vertices. The proof uses separation of the retained hole boxes and
their strict interiority, as well as actual sheet-transport injectivity.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid
open Purelib.Data.List
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann.Meshes
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (exteriorBoundaries boundaryLoops)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Flattening the original exterior components gives the two retained sheet walks in their actual parity-dependent
order. -/
theorem exteriorBoundaries_flatten (lifted : LiftedPuncturedGrid base) :
    lifted.exteriorBoundaries.flatten = lifted.edges.indexedEdges lifted.vertices base.bank.exterior 0 ++
      lifted.edges.indexedEdges lifted.vertices base.bank.exterior 1 := by
  cases shape : curve.degreeShape with
  | odd degree =>
      rw [exteriorBoundaries, shape]
      change _ ++ [] = _
      rw [Append.append_nil]
      rw [lifted.edges.indexedEdges_append, lifted.exterior_swap_odd degree, BranchCutLifts.otherSheet_zero]
  | even _ =>
      rw [exteriorBoundaries, shape]
      change _ ++ (_ ++ []) = _
      rw [Append.append_nil]

/-- The retained exterior component walks have distinct original start vertices across both sheets.

The flattened tours are exactly the original two indexed sheet walks. Their retained exterior simplicity and original
root transports certify distinct starts. -/
theorem exteriorBoundaries_simple (lifted : LiftedPuncturedGrid base) :
    (lifted.exteriorBoundaries.flatten.map OrientedEdge.start).Nodup := by
  rw [lifted.exteriorBoundaries_flatten]
  exact lifted.edges.twoSheetStarts_nodup lifted.vertices
    (fun point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop) base.bank.exterior
    (base.bank.frame.boundary_simple (RootRadius.Box.largeSquareBox_proper _))

/-- Each original exterior boundary start lies on an actual side of the ambient rectangle. -/
theorem exteriorBoundary_start_on_side (lifted : LiftedPuncturedGrid base) {vertex : Fin lifted.vertices.count}
    (member : vertex ∈ lifted.exteriorBoundaries.flatten.map OrientedEdge.start) :
    (lifted.vertices.coordinate vertex).re = (Cuts.Ambient curve).xLower ∨
    (lifted.vertices.coordinate vertex).re = (Cuts.Ambient curve).xUpper ∨
    (lifted.vertices.coordinate vertex).im = (Cuts.Ambient curve).yLower ∨
    (lifted.vertices.coordinate vertex).im = (Cuts.Ambient curve).yUpper := by
  rw [lifted.exteriorBoundaries_flatten, Map.map_append] at member
  apply base.bank.frame.boundary_start_on_side
  exact (Membership.mem_append.mp member).elim
    (lifted.edges.indexedStart_coordinate_mem lifted.vertices base.bank.exterior 0)
    (lifted.edges.indexedStart_coordinate_mem lifted.vertices base.bank.exterior 1)

/-- The original hole boundary components have distinct retained start vertices.

Each original hole tour is simple, and the supplied separated hole boxes exclude a shared coordinate between different
retained holes. -/
theorem holeBoundaries_simple (lifted : LiftedPuncturedGrid base) :
    (((base.faces.holes.map (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).flatten).map
      OrientedEdge.start).Nodup := by
  have collect : ∀ (holes : List (PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)),
      holes.Pairwise (fun first second => first.index ≠ second.index) →
      (((holes.map (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).flatten).map
        OrientedEdge.start).Nodup := by
    intro holes separated
    induction holes with
    | nil => exact .nil
    | cons first holes ih =>
        rw [List.map_cons, List.flatten_cons, Map.map_append]
        apply Nodup.nodup_append (first.liftedBoundary_simple lifted.vertices lifted.edges)
          (ih (List.pairwise_cons.mp separated).2)
        intro left leftMember right rightMember same
        rcases Map.mem_map.mp rightMember with ⟨edge, edgeMember, startEq⟩
        rcases SimpleBoundaryCycles.mem_flatten.mp edgeMember with ⟨boundary, boundaryMember, member⟩
        rcases Map.mem_map.mp boundaryMember with ⟨last, lastMember, boundaryEq⟩
        rw [← boundaryEq] at member
        have rightIn : right ∈ (last.liftedBoundary lifted.vertices lifted.edges).map OrientedEdge.start := by
          rw [← startEq]
          exact Map.mem_map_of_mem member
        exact (base.holes_separated first last ((List.pairwise_cons.mp separated).1 last lastMember)).points_ne
          (first.liftedBoundary_start_inside lifted.vertices lifted.edges leftMember)
          (last.liftedBoundary_start_inside lifted.vertices lifted.edges rightIn)
          (congrArg lifted.vertices.coordinate same)
  exact collect base.faces.holes base.faces.holes_pairwise

/-- Strict interiority of the original holes separates every hole boundary start from the exterior starts. -/
theorem exterior_hole_starts_disjoint (lifted : LiftedPuncturedGrid base)
    (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    {left right : Fin lifted.vertices.count}
    (exterior : left ∈ lifted.exteriorBoundaries.flatten.map OrientedEdge.start)
    (interior : right ∈ (hole.liftedBoundary lifted.vertices lifted.edges).map OrientedEdge.start) : left ≠ right := by
  intro same
  have sides := lifted.exteriorBoundary_start_on_side exterior
  rw [same] at sides
  have inside := hole.liftedBoundary_start_inside lifted.vertices lifted.edges interior
  have strict := base.hole_interior hole
  rcases sides with leftSide | rightSide | bottomSide | topSide
  · have bound := strict.left.trans_le inside.1
    rw [leftSide] at bound
    exact (lt_irrefl _) bound
  · have bound := inside.2.1.trans_lt strict.right
    rw [rightSide] at bound
    exact (lt_irrefl _) bound
  · have bound := strict.bottom.trans_le inside.2.2.1
    rw [bottomSide] at bound
    exact (lt_irrefl _) bound
  · have bound := inside.2.2.2.trans_lt strict.top
    rw [topSide] at bound
    exact (lt_irrefl _) bound

/-- Every physical boundary source vertex occurs exactly once over all displayed tours, including both sheet
occurrences.

The original exterior and hole tours are individually simple. Their strict geometric separation excludes any shared
retained start vertex across the two banks. -/
theorem boundaryLoops_starts_nodup (lifted : LiftedPuncturedGrid base) :
    (lifted.boundaryLoops.flatten.map OrientedEdge.start).Nodup := by
  rw [boundaryLoops, Flatten.flatten_append, Map.map_append]
  apply Nodup.nodup_append lifted.exteriorBoundaries_simple lifted.holeBoundaries_simple
  intro left leftMember right rightMember
  rcases Map.mem_map.mp rightMember with ⟨edge, edgeMember, startEq⟩
  rcases SimpleBoundaryCycles.mem_flatten.mp edgeMember with ⟨boundary, boundaryMember, member⟩
  rcases Map.mem_map.mp boundaryMember with ⟨hole, _, boundaryEq⟩
  rw [← boundaryEq] at member
  apply lifted.exterior_hole_starts_disjoint hole leftMember
  rw [← startEq]
  exact Map.mem_map_of_mem member

/-- Every retained original boundary component contains at least four oriented edges. -/
theorem boundaryLoops_min_length (lifted : LiftedPuncturedGrid base)
    {boundary : List (OrientedEdge lifted.vertices.count)} (member : boundary ∈ lifted.boundaryLoops) :
    4 ≤ boundary.length := by
  have exteriorCount : 4 ≤ base.bank.exterior.edgeCount :=
    base.bank.frame.boundary_edgeCount_ge_four (RootRadius.Box.largeSquareBox_proper _)
  rcases Membership.mem_append.mp member with exterior | holeMember
  · cases shape : curve.degreeShape with
    | odd degree =>
        rw [exteriorBoundaries, shape] at exterior
        have equal := Membership.mem_singleton.mp exterior
        rw [equal, lifted.edges.indexedEdges_length, Polynomial.Geometry.Grid.WindowSize.Walk.append_edgeCount]
        omega
    | even _ =>
        rw [exteriorBoundaries, shape] at exterior
        rcases Membership.mem_cons.mp exterior with equal | remaining
        · rw [equal, lifted.edges.indexedEdges_length]; exact exteriorCount
        · have equal := Membership.mem_singleton.mp remaining
          rw [equal, lifted.edges.indexedEdges_length]; exact exteriorCount
  · rcases Map.mem_map.mp holeMember with ⟨hole, _, rfl⟩
    rw [hole.liftedBoundary_length]
    decide

/-- No oriented edge is repeated in the original retained boundary component bank. -/
theorem boundaryLoops_edges_nodup (lifted : LiftedPuncturedGrid base) : lifted.boundaryLoops.flatten.Nodup :=
  SimpleBoundaryCycles.edges_nodup lifted.boundaryLoops_starts_nodup

/-- The original retained boundary component bank contains no edge together with its reverse. -/
theorem boundaryLoops_no_reverse (lifted : LiftedPuncturedGrid base)
    {edge : OrientedEdge lifted.vertices.count} (member : edge ∈ lifted.boundaryLoops.flatten) :
    edge.reverse ∉ lifted.boundaryLoops.flatten :=
  SimpleBoundaryCycles.flatten_no_reverse lifted.boundaryLoops_closed lifted.boundaryLoops_starts_nodup
    (fun _ member => Nat.le_trans (by decide) (lifted.boundaryLoops_min_length member)) member

/-- The actual closed tours give every exposed edge exactly once and no internal edge. In particular, there are no
hidden cancelling retracings.

The original coefficient-one and distinct-edge certificates identify each retained occurrence. Directed conversions
preserve both exposure conditions and exclude its reverse from the same tours. -/
theorem boundaryLoops_edge_iff (lifted : LiftedPuncturedGrid base) (edge : OrientedEdge lifted.vertices.count) :
    edge ∈ lifted.boundaryLoops.flatten ↔
      edge ∈ triangleEdgeOccurrences lifted.mesh.triangulation.faces ∧
        edge.reverse ∉ triangleEdgeOccurrences lifted.mesh.triangulation.faces := by
  have physical := PhysicalBoundaryChains.boundary_coefficient_one_iff lifted edge
  have counted := AreaChainTests.coefficient_eq_one_iff edge _ lifted.boundaryLoops_edges_nodup
  constructor
  · intro member
    exact physical.mp (counted.mpr ⟨member, lifted.boundaryLoops_no_reverse member⟩)
  · intro exposed
    exact (counted.mp (physical.mpr exposed)).1

/-- All fields are discharged from the actual cached grid and root transports. No boundary-component certificate is
supplied by the caller. -/
@[expose] def boundaryComponents (lifted : LiftedPuncturedGrid base) :
    PolygonStokes.BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces) where
  cycles := lifted.boundaryLoops
  closed := lifted.boundaryLoops_closed
  min_length := fun _ member => Nat.le_trans (by decide) (lifted.boundaryLoops_min_length member)
  sources_unique := lifted.boundaryLoops_starts_nodup
  edge_iff := lifted.boundaryLoops_edge_iff

/-- An original unpaired cut-edge occurrence projects exactly to an edge of the retained boundary components. -/
theorem cut_boundary_iff_boundaryComponents (lifted : LiftedPuncturedGrid base) (edge : OrientedEdge
  lifted.vertices.count) :
    edge ∈ lifted.cutBoundaryPairs.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
      edge ∈ lifted.boundaryComponents.cycles.flatten :=
  (lifted.cutBoundaryPairs_boundary_iff edge).trans (lifted.boundaryComponents.edge_iff edge).symm

/-- Euler balance now counts the certified, disjoint cycle decomposition of the actual exposed boundary, not merely a
stored list of closed tours. Attaching caps and comparing to the normal-form handles are subsequent steps. -/
theorem euler_add_boundaryComponents (lifted : LiftedPuncturedGrid base) :
    (((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.mesh.surfaceEdges.representatives.length +
      lifted.mesh.triangles.length) + lifted.boundaryComponents.cycles.length = 2 - 2 * genus :=
  LiftedPuncturedGrid.euler_add_boundary_tours lifted

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end
