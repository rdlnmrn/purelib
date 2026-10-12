module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
public import Purelib.Topology.Mesh.RectangleDetours
public import Purelib.Riemann.Meshes.GridLiftedDualSteps
public import Purelib.Riemann.Meshes.GridLiftedEdgeUniqueness
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.RootIsolation.SquareRoot.Grid.Walk

open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Surface.Cut.JumpPaths

public section

/-!
# Actual mesh edges as root-transported grid walks

Every triangular edge is routed along the sides of its retained regular
rectangle. The selected lift and edge kind remain available, including for
diagonals, so subsequent integral comparisons can use that very face.
The finite lookup consumes a proof of support, not a search-success premise.
-/

namespace Purelib.Riemann.Meshes

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces LiftedMesh)
open Purelib.Topology.Polygon.Stokes (triangleEdgeOccurrences)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace GridLiftedFaces.BranchCellBank.LiftedFace

variable {face : RegularFace bank} {sheet : Fin 2}

/-- Read the original lifted rectangle side as its retained grid edge walk with exact indexed endpoints. -/
@[expose] def sideWalk (lifted : LiftedFace
  vertices edges face sheet) (side : GridSide) :
    Vertex.VertexWalk vertices edges (lifted.quad.edge side.kind).start (lifted.quad.edge side.kind).finish :=
  (VertexWalk.ofEdge vertices edges (face.side side) (lifted.sideStartSheet side)).castVertices
    (congrArg OrientedEdge.start (lifted.side_edge_eq side).symm)
    (congrArg OrientedEdge.finish (lifted.side_edge_eq side).symm)

open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace (sideWalk)

/-- The retained rectangle-side walk has exactly the original singleton indexed side edge. -/
theorem sideWalk_indexed (lifted : LiftedFace
  vertices edges face sheet) (side : GridSide) :
    (lifted.sideWalk side).indexed = [lifted.quad.edge side.kind] := by
  rw [sideWalk, VertexWalk.castVertices_indexed, VertexWalk.ofEdge_indexed, lifted.side_edge_eq]

open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace (sideWalk_indexed)

/-- Route an original triangle edge along retained rectangle sides.

Diagonal cases use the same bottom-right detour and its root-coherent reverse on the original selected face. -/
@[expose] def edgeWalk (lifted : LiftedFace
  vertices edges face sheet) : (kind : RectangleEdge.Kind) →
    Vertex.VertexWalk vertices edges (lifted.quad.edge kind).start (lifted.quad.edge kind).finish
  | .bottom => lifted.sideWalk .bottom
  | .right => lifted.sideWalk .right
  | .top => lifted.sideWalk .top
  | .left => lifted.sideWalk .left
  | .upDiagonal => (lifted.sideWalk .bottom).append (lifted.sideWalk .right)
  | .downDiagonal => ((lifted.sideWalk .bottom).append (lifted.sideWalk .right)).reverse
      (fun point member => (BranchCellBank.referenceAt bank point member).toLoop)

open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace (edgeWalk)

/-- The retained routed walk has exactly the original rectangle edge's indexed detour word.

The original side walks retain their singleton indexed edges. Concatenation and reversal read exactly the displayed
rectangle detour without rebuilding the selected face or changing its sheet. -/
theorem edgeWalk_indexed (lifted : LiftedFace
  vertices edges face sheet) (kind : RectangleEdge.Kind) :
    (lifted.edgeWalk kind).indexed = lifted.quad.detour kind := by
  cases kind with
  | bottom => exact sideWalk_indexed lifted .bottom
  | right => exact sideWalk_indexed lifted .right
  | top => exact sideWalk_indexed lifted .top
  | left => exact sideWalk_indexed lifted .left
  | upDiagonal =>
      change (lifted.sideWalk .bottom).indexed ++ (lifted.sideWalk .right).indexed = _
      rw [sideWalk_indexed, sideWalk_indexed]
      rfl
  | downDiagonal =>
      change CutPath.reverse ((lifted.sideWalk .bottom).indexed ++ (lifted.sideWalk .right).indexed) = _
      rw [sideWalk_indexed, sideWalk_indexed]
      rfl

end GridLiftedFaces.BranchCellBank.LiftedFace

namespace GridLiftedMesh.LiftedFaces

set_option genInjectivity false in
/-- The exact retained rectangle and oriented edge used by the route.

The original bounded position and sheet identify the actual selected lifted face. Its directed edge equality and
membership witness retain that face inside the unchanged complete triangle bank. -/
structure EdgeLocation {faces : List (RegularFace bank)} (lifts
  : LiftedFaces vertices edges faces)
    (edge : OrientedEdge vertices.count) where
  /-- The retained original regular face containing the selected edge occurrence. -/ face : RegularFace bank
  /-- The exact bounded position of the retained face in the original face list. -/ position : Fin faces.length
  /-- The retained face is exactly the original list entry at its bounded position. -/ face_eq : faces[position.val] =
    face
  /-- The original selected lifted-face sheet. -/ sheet : Fin 2
  /-- The retained original lift of the selected face and sheet. -/ lifted : LiftedFace vertices edges face sheet
  /-- The retained directed rectangle edge kind of the original triangle-edge occurrence. -/ kind : RectangleEdge.Kind
  /-- The selected lifted rectangle edge equals the original requested indexed edge. -/ edge_eq : lifted.quad.edge kind
    = edge
  /-- Every edge occurrence of the selected original lifted face belongs to the complete retained triangle edge list. -/
    retained : ∀ candidate ∈ lifted.quad.triangles.flatMap OrientedTriangle.boundary,
    candidate ∈ lifts.triangles.flatMap OrientedTriangle.boundary

constructive_injectivity Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)

/-- Locate the original supported triangle edge in the retained lifted-face list, preserving its exact face position,
sheet and directed edge kind. -/
@[expose] def locateEdge : {faces : List (RegularFace bank)} →
  (lifts : LiftedFaces vertices edges faces) →
    (edge : OrientedEdge vertices.count) → edge ∈ lifts.triangles.flatMap OrientedTriangle.boundary →
      EdgeLocation lifts edge
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons zero one tail, edge, member =>
      if found : edge ∈ zero.quad.triangles.flatMap OrientedTriangle.boundary then
        let kind := Purelib.Topology.Mesh.RectangleDetours.kindOfEdge zero.quad edge found
        ⟨_, 0, rfl, 0, zero, kind.val, kind.property, fun _ belongs => by
          rw [LiftedFaces.triangleEdges_cons]
          exact Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr (Or.inl belongs)))⟩
      else if foundOne : edge ∈ one.quad.triangles.flatMap OrientedTriangle.boundary then
        let kind := Purelib.Topology.Mesh.RectangleDetours.kindOfEdge one.quad edge foundOne
        ⟨_, 0, rfl, 1, one, kind.val, kind.property, fun _ belongs => by
          rw [LiftedFaces.triangleEdges_cons]
          exact Membership.mem_append.mpr (Or.inl (Membership.mem_append.mpr (Or.inr belongs)))⟩
      else
        let located := tail.locateEdge edge (by
          rw [LiftedFaces.triangleEdges_cons] at member
          exact (Membership.mem_append.mp member).resolve_left (fun localMember =>
            (Membership.mem_append.mp localMember).elim found foundOne))
        ⟨located.face, located.position.succ, located.face_eq, located.sheet,
          located.lifted, located.kind, located.edge_eq, fun candidate belongs => by
            rw [LiftedFaces.triangleEdges_cons]
            exact Membership.mem_append.mpr (Or.inr (located.retained candidate belongs))⟩

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation locateEdge)

namespace EdgeLocation

variable {faces : List (RegularFace bank)} {lifts : LiftedFaces vertices edges faces} {edge : OrientedEdge
  vertices.count}

/-- The retained edge location's actual face belongs to the original face list. -/
theorem member (location : EdgeLocation lifts
  edge) : location.face ∈ faces :=
  (congrArg (fun face => face ∈ faces) location.face_eq).mp (List.getElem_mem _)

/-- Read the retained original face detour as a root-transported walk between the requested indexed endpoints. -/
@[expose] def walk (location : EdgeLocation lifts
  edge) : Vertex.VertexWalk vertices edges edge.start edge.finish :=
  (location.lifted.edgeWalk location.kind).castVertices
    (congrArg OrientedEdge.start location.edge_eq) (congrArg OrientedEdge.finish location.edge_eq)

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation (walk)

/-- The retained edge-location walk reads exactly the original selected rectangle detour. -/
theorem walk_indexed (location : EdgeLocation
  lifts edge) :
    location.walk.indexed = location.lifted.quad.detour location.kind := by
  rw [walk, VertexWalk.castVertices_indexed, location.lifted.edgeWalk_indexed]

/-- Every retained detour edge is supported by the original complete triangle-edge list. -/
theorem walk_supported (location : EdgeLocation
  lifts edge) :
    CutPath.Supported (lifts.triangles.flatMap OrientedTriangle.boundary) location.walk.indexed := by
  rw [location.walk_indexed]
  exact CutPath.supported_mono (RectangleDetours.detour_supported location.lifted.quad location.kind) location.retained

end EdgeLocation
end GridLiftedMesh.LiftedFaces

namespace GridLiftedMesh.LiftedMesh

variable {faces : PuncturedFaces bank}

/-- Locate an original supported triangulation edge in the same retained lifted mesh face bank. -/
@[expose] def locateEdge (mesh : LiftedMesh vertices edges
  faces) (edge : OrientedEdge vertices.count)
    (member : edge ∈ triangleEdgeOccurrences mesh.triangulation.faces) :
    LiftedFaces.EdgeLocation mesh.lifts edge :=
  mesh.lifts.locateEdge edge (by rw [← mesh.triangleEdges_eq]; exact member)

end GridLiftedMesh.LiftedMesh
end Purelib.Riemann.Meshes
