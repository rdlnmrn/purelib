module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.List.Permutation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.GridLiftedEdgeConnections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Topology.Surface.Cut.JumpPaths
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

public section

/-!
# Automatic face assignments for the actual lifted grid skeleton

Every grid edge has a retained regular incident face, including frame edges
and reversed hole boundaries. Endpoint transport identifies the selected
face side with the actual lifted edge. Thus an existing grid walk needs no
caller-supplied support certificate to enter the shared face comparisons.
No walk is rerouted and no root preparation is replaced by this assignment.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Integration.PuncturedVertexStars

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

open Purelib.Riemann.Meshes.PuncturedEdgeFaces

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

/-- Endpoint equality identifies the two retained lifted edge occurrences through their actual root transport.

The two endpoint equalities identify the source and target points of the supplied grid edges. Their retained endpoint
root references certify equality of the indexed occurrences at the same sheet. -/
private theorem indexedEdge_same {start finish otherStart otherFinish : Data.Gaussian.Basic.Canonical}
    (edge : Walks.Edge base.bank.grid start finish) (other : Walks.Edge base.bank.grid otherStart otherFinish)
    (first : otherStart = start) (last : otherFinish = finish) (sheet : Fin 2) :
    edges.indexedEdge vertices other sheet = edges.indexedEdge vertices edge sheet := by
  cases first
  cases last
  exact edges.indexedEdge_eq vertices other edge (BranchCellBank.referenceAt base.bank.toBranchCellBank _
    edge.vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ edge.vertices.2).toLoop sheet

/-- Every side of a retained lifted quadrilateral occurs in one of its two original mesh triangles.

The located face retains its original triangulation occurrence. Membership in that occurrence's side list embeds the
same oriented side in the mesh triangle-edge bank. -/
private theorem quadSide_member {position : Fin base.faces.regulars.length} {sheet : Fin 2}
    (located : mesh.LocatedFace position sheet) (side : GridLiftedDualSteps.GridSide) :
    located.lifted.quad.edge side.kind ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces :=
  Flatten.mem_flatMap.mpr ⟨_, Permutation.ofFn_mem _ _, located.occurrence.edge_mem side.kind⟩

/-- The support proof uses actual root transport, not only matching planar endpoints.

The original edge and its sheet determine an incident retained face and side. Its orientation and endpoint transport
place the actual indexed edge, or its reversal, in the original mesh triangle-edge list. -/
theorem indexedEdge_supported (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {start finish : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge base.bank.grid start finish) (sheet : Fin 2) :
    edges.indexedEdge vertices edge sheet ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      (edges.indexedEdge vertices edge sheet).reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces := by
  let cell := RegularEdgeCell.acquire (VertexStar.build base start edge.vertices.1) edge
  let first := cell.first.lift mesh sheet
  let located := first.value.located
  let side := base.faces.regulars[cell.located.index.val].side cell.geometry.side
  have cellEq : base.faces.regulars[cell.located.index.val].cell = cell.geometry.cell := cell.first.indexed_cell
  have member := Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.quadSide_member located
    cell.geometry.side
  rw [located.lifted.side_edge_eq] at member
  cases orientation : cell.geometry.reversed with
  | false =>
      have firstEq : cell.geometry.side.start cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation] at retained
        exact retained
      have lastEq : cell.geometry.side.finish cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation] at retained
        exact retained
      rw [first.startSheet_at cell.geometry.side firstEq] at member
      have same := Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedEdge_same (edges := edges)
        (vertices := vertices) edge side
        (by rw [cellEq]; exact firstEq)
        (by rw [cellEq]; exact lastEq) sheet
      exact Or.inl (same ▸ member)
  | true =>
      have firstEq : cell.geometry.side.finish cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [orientation] at retained
        exact retained
      have lastEq : cell.geometry.side.start cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [orientation] at retained
        exact retained
      have opposite := edges.indexedEdge_opposite_of_endpoints vertices side edge
        (by rw [cellEq]; exact firstEq.symm)
        (by rw [cellEq]; exact lastEq.symm)
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ side.vertices.1).toLoop
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ side.vertices.2).toLoop
        (located.lifted.sideStartSheet cell.geometry.side)
      have transported : (edges.edge side).forward.target (located.lifted.sideStartSheet cell.geometry.side) = sheet :=
        (located.lifted.side_transport cell.geometry.side).trans (first.finishSheet_at cell.geometry.side firstEq)
      rw [transported] at opposite
      have reversed := congrArg OrientedEdge.reverse opposite
      rw [OrientedEdge.reverse_reverse] at reversed
      exact Or.inr (reversed.symm ▸ member)

/-- Every edge occurrence of the original lifted grid walk is supported by an original mesh triangle, up to reversal.

Structural induction follows the supplied walk without rerouting it. Each edge uses its actual indexed occurrence and
the inherited terminal sheet of the preceding root transport. -/
theorem indexedWalk_supported (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start finish) (sheet : Fin 2),
    CutPath.Supported
      (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) (edges.indexedEdges vertices walk sheet)
  | _, _, .nil _, _ => fun _ member => (List.not_mem_nil member).elim
  | _, _, .cons edge tail, sheet => by
      intro candidate member
      rcases Membership.mem_cons.mp member with rfl | member
      · exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedEdge_supported mesh edge sheet
      · exact Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported mesh tail
          ((edges.edge edge).forward.target sheet) candidate member

/-- Materialize the actual indices once, then locate their retained faces.

The indexed edge list is cached from the supplied walk and initial sheet. Its support certificate locates those same
occurrences in the retained mesh, preserving the original path and edge order. -/
@[expose] def walkFaces (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start finish) (sheet : Fin 2) :
      LiftedMesh.PathFaces mesh walk.path :=
  let indexed := edges.indexedEdges vertices walk sheet
  PathFaces.ofIndexed mesh walk indexed ⟨sheet, rfl⟩
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported mesh walk sheet)

/-- Automatic face assignment reads back exactly the original lifted walk's retained indexed edges.

The face assignment is built from the once-materialized indexed list. Its readback law returns that same list for the
supplied original walk and sheet. -/
theorem walkFaces_indexed (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start finish) (sheet : Fin 2) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces mesh walk sheet).indexed =
      edges.indexedEdges vertices walk sheet :=
  PathFaces.ofIndexed_indexed mesh walk _ _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
