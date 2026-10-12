module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

/-!
# Exact edge enumeration and Euler number of the punctured double cover

Add one positive diagonal from each retained root-backed quadrilateral to
the complete lifted grid skeleton. This is a duplicate-free set of oriented
representatives of all actual mesh edges modulo reversal. Together with the
actual vertex and face counts it computes the punctured surface's Euler
number. Identifying the normal-form handle count is a further theorem.
-/

section

open Purelib
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedFaces
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.PolygonStokes

set_option genInjectivity false in
/-- One displayed orientation of every edge in the occurrence list, with literal duplicates and reverse duplicates
excluded. This certificate counts actual finite incidence rather than relying on a particular cancellation schedule.

The retained occurrence list determines support and coverage. Every displayed representative is unique, excludes its
reverse and accounts for the same original oriented incidences. -/
structure EdgeRepresentativeBank {vertices : Nat} (occurrences : List (Stokes.OrientedEdge vertices)) where
  /-- The retained oriented representatives of the original finite edge occurrences. -/ representatives : List
    (Stokes.OrientedEdge vertices)
  /-- The retained oriented representative list has no duplicate. -/ unique : representatives.Nodup
  /-- No retained representative's reverse also occurs in the original bank. -/ no_reverse : ∀ edge ∈ representatives,
    edge.reverse ∉ representatives
  /-- Each retained representative or its reverse is an actual original edge occurrence. -/ supported : ∀ edge ∈
    representatives, edge ∈ occurrences ∨ edge.reverse ∈ occurrences
  /-- Every original edge occurrence has one orientation in the retained representative list. -/ covers : ∀ edge ∈
    occurrences, edge ∈ representatives ∨ edge.reverse ∈ representatives

constructive_injectivity EdgeRepresentativeBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.PolygonStokes

end

section

open Purelib
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedFaces
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges (PositiveAxis)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.PolygonStokes (EdgeRepresentativeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

section

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}

namespace Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- The sum of the original vertex coordinates orders positive grid edges and diagonals. -/
@[expose] def edgeHeight (vertices :
  LiftedVertices.VertexBank grid) (vertex : Fin vertices.count) : Fraction.Rational :=
  (vertices.coordinate vertex).re + (vertices.coordinate vertex).im

/-- A positive original grid-axis edge strictly increases the retained coordinate-sum height. -/
theorem axis_increasing (vertices :
  LiftedVertices.VertexBank grid) {edge : Stokes.OrientedEdge vertices.count}
    (positive : SkeletonEdges.PositiveAxis vertices edge) : vertices.edgeHeight edge.start < vertices.edgeHeight
      edge.finish := by
  unfold LiftedVertices.VertexBank.edgeHeight
  rcases positive with ⟨horizontal, level⟩ | ⟨level, vertical⟩
  · rw [level]
    exact Fraction.Order.Arithmetic.add_lt_add_right_direct horizontal _
  · rw [level]
    exact Fraction.Order.Arithmetic.add_lt_add_left_direct vertical _

end Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

section

variable {face : RegularFace bank} {sheet : Fin 2}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- The original lifted face diagonal strictly increases both actual coordinate components. -/
theorem diagonal_positive (lifted :
  BranchCellBank.LiftedFace vertices edges face sheet) :
    (vertices.coordinate (lifted.quad.edge .upDiagonal).start).re <
        (vertices.coordinate (lifted.quad.edge .upDiagonal).finish).re ∧
      (vertices.coordinate (lifted.quad.edge .upDiagonal).start).im <
        (vertices.coordinate (lifted.quad.edge .upDiagonal).finish).im := by
  change (vertices.coordinate lifted.quad.first).re < (vertices.coordinate lifted.quad.third).re ∧
    (vertices.coordinate lifted.quad.first).im < (vertices.coordinate lifted.quad.third).im
  rw [lifted.coordinates.1, lifted.coordinates.2.2.1]
  exact face.cell.box_proper

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace

/-- Each original lifted face side occurs in the retained grid skeleton up to reversal. -/
private theorem side_skeleton (lifted : BranchCellBank.LiftedFace vertices edges face sheet) (side :
  GridLiftedDualSteps.GridSide) :
    lifted.quad.edge side.kind ∈ edges.skeleton vertices ∨
      (lifted.quad.edge side.kind).reverse ∈ edges.skeleton vertices := by
  rw [lifted.side_edge_eq]
  exact edges.indexedEdge_skeleton vertices (fun point member => (BranchCellBank.referenceAt bank point member).toLoop)
    _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- Every original lifted rectangle edge is a retained skeleton edge or that face's actual diagonal, up to reversal. -/
theorem edge_skeleton_or_diagonal (lifted :
  BranchCellBank.LiftedFace vertices edges face sheet) (kind : RectangleEdge.Kind) :
    (lifted.quad.edge kind ∈ edges.skeleton vertices ∨ (lifted.quad.edge kind).reverse ∈ edges.skeleton vertices) ∨
      lifted.quad.edge kind = lifted.quad.edge .upDiagonal ∨ (lifted.quad.edge kind).reverse = lifted.quad.edge
        .upDiagonal := by
  cases kind with
  | bottom =>
    exact Or.inl
      (SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace.side_skeleton lifted
      .bottom)
  | right =>
    exact Or.inl
      (SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace.side_skeleton lifted
      .right)
  | downDiagonal => exact Or.inr (Or.inr rfl)
  | upDiagonal => exact Or.inr (Or.inl rfl)
  | top =>
    exact Or.inl
      (SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace.side_skeleton lifted
      .top)
  | left =>
    exact Or.inl
      (SurfaceEdges.ClearGrid.BranchCellBank.LiftedFace.side_skeleton lifted
      .left)

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

end

section

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces

/-- Enumerate the positive diagonal of each original retained lifted face in face and sheet order. -/
@[expose] def diagonals : {faces : List
  (PuncturedGridFaces.RegularFace bank)} → GridLiftedMesh.LiftedFaces vertices edges faces → List (Stokes.OrientedEdge
  vertices.count)
  | _, .nil => []
  | _, .cons zero one tail => zero.quad.edge .upDiagonal :: one.quad.edge .upDiagonal :: tail.diagonals

/-- There are exactly two retained diagonals for each original regular base face. -/
theorem diagonals_length : ∀ {faces : List
  (PuncturedGridFaces.RegularFace bank)} (lifts : GridLiftedMesh.LiftedFaces vertices edges faces),
    lifts.diagonals.length = 2 * faces.length
  | _, .nil => rfl
  | _, .cons _ _ tail => by
      simp only [diagonals, List.length_cons, tail.diagonals_length]
      omega

/-- Each retained diagonal is an original oriented triangle occurrence, not a new geometric chord inserted after
computing the mesh. -/
theorem diagonals_sublist : ∀ {faces : List
  (PuncturedGridFaces.RegularFace bank)} (lifts : GridLiftedMesh.LiftedFaces vertices edges faces),
    lifts.diagonals.Sublist (lifts.triangles.flatMap OrientedTriangle.boundary)
  | _, .nil => .slnil
  | _, .cons _ _ tail =>
      .cons _ (.cons _ (.cons _ (.cons_cons _ (.cons _ (.cons _
        (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons _ (.cons _ tail.diagonals_sublist)))))))))))

/-- Every retained diagonal strictly increases both original coordinate components. -/
theorem diagonals_positive : ∀ {faces : List
  (PuncturedGridFaces.RegularFace bank)} (lifts : GridLiftedMesh.LiftedFaces vertices edges faces)
    {edge : Stokes.OrientedEdge vertices.count}, edge ∈ lifts.diagonals →
      (vertices.coordinate edge.start).re < (vertices.coordinate edge.finish).re ∧
        (vertices.coordinate edge.start).im < (vertices.coordinate edge.finish).im
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons zero one tail, edge, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact zero.diagonal_positive
      · rcases Membership.mem_cons.mp member with rfl | member
        · exact one.diagonal_positive
        · exact tail.diagonals_positive member

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.BranchCellBank.LiftedFaces

/-- Every edge occurrence in one original lifted face is represented by its retained skeleton or diagonal. -/
private theorem local_covered {face : PuncturedGridFaces.RegularFace bank} {sheet : Fin 2}
    (lifted : BranchCellBank.LiftedFace vertices edges face sheet) {edge : Stokes.OrientedEdge vertices.count}
    (member : edge ∈ lifted.quad.triangles.flatMap OrientedTriangle.boundary) :
    (edge ∈ edges.skeleton vertices ∨ edge.reverse ∈ edges.skeleton vertices) ∨
      edge = lifted.quad.edge .upDiagonal ∨ edge.reverse = lifted.quad.edge .upDiagonal := by
  rw [IndexedQuadrilateral.triangleEdges_eq lifted.quad] at member
  obtain ⟨kind, _, rfl⟩ := Map.mem_map.mp member
  exact lifted.edge_skeleton_or_diagonal kind

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.BranchCellBank.LiftedFaces

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.BranchCellBank.LiftedFaces in
/-- The retained skeleton and original face diagonals cover every actual lifted triangle edge up to reversal. -/
theorem edges_covered : ∀ {faces : List
  (PuncturedGridFaces.RegularFace bank)} (lifts : GridLiftedMesh.LiftedFaces vertices edges faces)
    {edge : Stokes.OrientedEdge vertices.count}, edge ∈ lifts.triangles.flatMap OrientedTriangle.boundary →
      (edge ∈ edges.skeleton vertices ∨ edge.reverse ∈ edges.skeleton vertices) ∨
        edge ∈ lifts.diagonals ∨ edge.reverse ∈ lifts.diagonals
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons zero one tail, edge, member => by
      rw [LiftedFaces.triangleEdges_cons] at member
      rcases Membership.mem_append.mp member with localMember | tailMember
      · rcases Membership.mem_append.mp localMember with zeroMember | oneMember
        · rcases SurfaceEdges.ClearGrid.BranchCellBank.LiftedFaces.local_covered zero zeroMember with skeleton | same |
          reversed
          · exact Or.inl skeleton
          · exact Or.inr (Or.inl (Membership.mem_cons.mpr (Or.inl same)))
          · exact Or.inr (Or.inr (Membership.mem_cons.mpr (Or.inl reversed)))
        · rcases SurfaceEdges.ClearGrid.BranchCellBank.LiftedFaces.local_covered one oneMember with skeleton | same |
          reversed
          · exact Or.inl skeleton
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (Membership.mem_cons.mpr (Or.inl same))))
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (Membership.mem_cons.mpr (Or.inl reversed))))
      · rcases tail.edges_covered tailMember with skeleton | direct | reversed
        · exact Or.inl skeleton
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ direct)))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ reversed)))

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces

end

section

variable {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

/-- The actual lifted mesh edge representatives: retained positive grid edges followed by original positive face
diagonals. -/
@[expose] def edgeRepresentatives (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) : List (Stokes.OrientedEdge vertices.count) :=
  edges.skeleton vertices ++ mesh.lifts.diagonals

/-- The retained mesh edge count is twice the sum of original horizontal, vertical and regular-face counts. -/
theorem edgeRepresentatives_length (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    mesh.edgeRepresentatives.length = 2 * (base.bank.grid.xIntervals.length * base.bank.grid.horizontal.length +
      base.bank.grid.yIntervals.length * base.bank.grid.vertical.length + base.faces.regulars.length) := by
  rw [edgeRepresentatives, Append.length_append, edges.skeleton_length,
    mesh.lifts.diagonals_length, Nat.mul_add]
  ring1

/-- The original lifted mesh edge representatives have no repeated oriented edge. -/
theorem edgeRepresentatives_nodup (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) : mesh.edgeRepresentatives.Nodup := by
  have unique := mesh.orientedEdges_unique
  rw [mesh.triangleEdges_eq] at unique
  refine Nodup.nodup_append (edges.skeleton_nodup vertices) (mesh.lifts.diagonals_sublist.nodup unique) ?_
  intro first firstMember last lastMember same
  have positive := mesh.lifts.diagonals_positive lastMember
  rw [← same] at positive
  rcases edges.skeleton_positive vertices firstMember with ⟨_, level⟩ | ⟨level, _⟩
  · exact ne_of_lt positive.2 level
  · exact ne_of_lt positive.1 level

/-- Every retained original edge representative strictly increases coordinate-sum height. -/
theorem edgeRepresentatives_increasing (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {edge : Stokes.OrientedEdge vertices.count} (member : edge ∈ mesh.edgeRepresentatives) :
    vertices.edgeHeight edge.start < vertices.edgeHeight edge.finish := by
  rcases Membership.mem_append.mp member with skeleton | diagonal
  · exact vertices.axis_increasing (edges.skeleton_positive vertices skeleton)
  · have positive := mesh.lifts.diagonals_positive diagonal
    exact Fraction.Order.Arithmetic.add_lt_add_direct positive.1 positive.2

/-- The retained original edge representative bank cannot contain both orientations of an edge. -/
theorem edgeRepresentatives_no_reverse (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {edge : Stokes.OrientedEdge vertices.count} (member : edge ∈ mesh.edgeRepresentatives) : edge.reverse ∉
      mesh.edgeRepresentatives := by
  intro reversed
  have forward := mesh.edgeRepresentatives_increasing (edge := edge) member
  have backward := mesh.edgeRepresentatives_increasing (edge := edge.reverse) reversed
  exact lt_asymm forward backward

/-- Every retained edge representative is supported by an actual original lifted triangle, up to reversal. -/
theorem edgeRepresentatives_supported (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {edge : Stokes.OrientedEdge vertices.count} (member : edge ∈ mesh.edgeRepresentatives) :
    edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨ edge.reverse ∈ Stokes.triangleEdgeOccurrences
      mesh.triangulation.faces := by
  rcases Membership.mem_append.mp member with skeleton | diagonal
  · exact LiftedMesh.skeleton_supported mesh skeleton
  · left
    rw [mesh.triangleEdges_eq]
    exact mesh.lifts.diagonals_sublist.subset diagonal

/-- Every original lifted triangle edge has exactly one orientation represented in the retained bank. -/
theorem edgeRepresentatives_cover (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {edge : Stokes.OrientedEdge vertices.count} (member : edge ∈ Stokes.triangleEdgeOccurrences
      mesh.triangulation.faces) :
    edge ∈ mesh.edgeRepresentatives ∨ edge.reverse ∈ mesh.edgeRepresentatives := by
  rw [mesh.triangleEdges_eq] at member
  rcases mesh.lifts.edges_covered member with skeleton | diagonal | reversed
  · exact skeleton.elim (fun member => Or.inl (Membership.mem_append.mpr (Or.inl member)))
      (fun member => Or.inr (Membership.mem_append.mpr (Or.inl member)))
  · exact Or.inl (Membership.mem_append.mpr (Or.inr diagonal))
  · exact Or.inr (Membership.mem_append.mpr (Or.inr reversed))

set_option genInjectivity false in
/-- Cached representatives count each actual unoriented mesh edge once.

No successful edge-matching check is supplied by the caller. -/
structure SurfaceEdges (mesh : GridLiftedMesh.LiftedMesh
  vertices edges base.faces) extends
    SurfaceEdges.PolygonStokes.EdgeRepresentativeBank
      (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) where
  /-- The retained representative count equals the exact original horizontal, vertical and regular-face formula. -/
    length_eq : representatives.length = 2 * (base.bank.grid.xIntervals.length * base.bank.grid.horizontal.length +
    base.bank.grid.yIntervals.length * base.bank.grid.vertical.length + base.faces.regulars.length)

constructive_injectivity Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SurfaceEdges

/-- Construct the exact finite edge representative certificate from the original lifted mesh and cached root transports.
-/
@[expose] def surfaceEdges (mesh : GridLiftedMesh.LiftedMesh
  vertices edges base.faces) : SurfaceEdges mesh where
  representatives := mesh.edgeRepresentatives
  unique := mesh.edgeRepresentatives_nodup
  no_reverse := fun _ => mesh.edgeRepresentatives_no_reverse
  supported := fun _ => mesh.edgeRepresentatives_supported
  covers := fun _ => mesh.edgeRepresentatives_cover
  length_eq := mesh.edgeRepresentatives_length

/-- Euler's number for the actual punctured mesh.

The counts refer to checked triangle vertices and edge representatives, not allocation sizes or an abstract
genus-labelled replacement complex. -/
theorem punctured_euler (mesh : GridLiftedMesh.LiftedMesh
  vertices edges base.faces)
    (vertexBank : ActiveVertices mesh) (edgeBank : SurfaceEdges
      mesh) :
    (vertexBank.indices.length : Int) - edgeBank.representatives.length + mesh.triangles.length =
      2 - 2 * curve.polynomial.natDegree := by
  have partition := base.faces.regulars_degree
  rw [Polynomial.Geometry.Grid.WindowSize.cells_length base.bank.grid] at partition
  have integerPartition := congrArg (fun count : Nat => (count : Int)) partition
  rw [Int.natCast_add, Int.natCast_mul] at integerPartition
  rw [vertexBank.length_eq_intervals, edgeBank.length_eq, mesh.faceCount,
    base.bank.frame.vertical_length, base.bank.frame.horizontal_length]
  simp only [Int.natCast_mul, Int.natCast_add, Nat.cast_one, Nat.cast_ofNat]
  have degreeEq : (curve.polynomial.natDegree : Int) =
      (base.bank.grid.xIntervals.length : Int) * base.bank.grid.yIntervals.length - base.faces.regulars.length := by
        omega
  rw [degreeEq]
  ring1

/-- The generic construction discharges both enumeration certificates. -/
theorem automatic_punctured_euler (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    ((LiftedMesh.activeVertices mesh).indices.length : Int) - mesh.surfaceEdges.representatives.length +
      mesh.triangles.length =
      2 - 2 * curve.polynomial.natDegree :=
  mesh.punctured_euler (LiftedMesh.activeVertices mesh) mesh.surfaceEdges

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

end
end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.LiftedPuncturedGrid

/-- The actual counts have the required genus balance in both degree parities.

The added count is explicitly that of the stored closed tours: identifying them with disjoint boundary components and
filling their caps must still be proved before treating this as a closed-surface Euler law. -/
theorem euler_add_boundary_tours (lifted : Meshes.LiftedPuncturedGrid base) :
    (((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.mesh.surfaceEdges.representatives.length +
      lifted.mesh.triangles.length) + lifted.boundaryLoops.length = 2 - 2 * genus := by
  rw [lifted.mesh.automatic_punctured_euler, lifted.boundaryLoops_count]
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [degree, Int.natCast_add, Int.natCast_mul, Nat.cast_ofNat]
      ring1
  | even degree =>
      simp only [degree, Int.natCast_add, Int.natCast_mul, Nat.cast_ofNat]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SurfaceEdges.ClearGrid.LiftedPuncturedGrid

end
end

end
