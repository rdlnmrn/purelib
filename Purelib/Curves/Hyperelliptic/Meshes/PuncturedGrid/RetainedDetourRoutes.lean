module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Mesh.RectangleDetours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib

@[expose] public section

/-!
# Side detours retaining the original lifted face

Expanding a diagonal must not look its sides up afresh: a reversed shared
side could then select the adjacent face's independent primitive cache.
These spines reuse the original face, sheet and position on every detour.
They contain geometry only, before any primitive accuracy is selected.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine)
open Purelib.Topology.Surface.Cut.JumpPaths
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
  {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}

section

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

/-- Retain the same original face, sheet and cached location while selecting another edge kind of its quadrilateral. -/
def atKind {edge : OrientedEdge vertices.count} (location : EdgeLocation mesh.lifts edge) (kind : RectangleEdge.Kind) :
    EdgeLocation mesh.lifts (location.lifted.quad.edge kind) :=
  ⟨location.face, location.position, location.face_eq, location.sheet, location.lifted, kind, rfl, location.retained⟩

/-- Expand the retained edge into its original face's side detour without repeating a geometric lookup. -/
def detourRoutes {edge : OrientedEdge vertices.count} (location : EdgeLocation mesh.lifts edge) :
    (kind : RectangleEdge.Kind) → MeshPathWalks.RouteSpine mesh (location.lifted.quad.detour kind)
  | .bottom => .cons (.forward (location.atKind .bottom)) .nil
  | .right => .cons (.forward (location.atKind .right)) .nil
  | .top => .cons (.forward (location.atKind .top)) .nil
  | .left => .cons (.forward (location.atKind .left)) .nil
  | .upDiagonal => .cons (.forward (location.atKind .bottom)) (.cons (.forward (location.atKind .right)) .nil)
  | .downDiagonal => .cons (.backward (location.atKind .right)) (.cons (.backward (location.atKind .bottom)) .nil)

/-- Reverse the original side detour while preserving every retained face, sheet and location. -/
def reverseDetourRoutes {edge : OrientedEdge vertices.count} (location : EdgeLocation mesh.lifts edge) :
    (kind : RectangleEdge.Kind) → MeshPathWalks.RouteSpine mesh (CutPath.reverse (location.lifted.quad.detour kind))
  | .bottom => .cons (.backward (location.atKind .bottom)) .nil
  | .right => .cons (.backward (location.atKind .right)) .nil
  | .top => .cons (.backward (location.atKind .top)) .nil
  | .left => .cons (.backward (location.atKind .left)) .nil
  | .upDiagonal => .cons (.backward (location.atKind .right)) (.cons (.backward (location.atKind .bottom)) .nil)
  | .downDiagonal => .cons (.forward (location.atKind .bottom)) (.cons (.forward (location.atKind .right)) .nil)

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

end

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

/-- Expand the retained edge into its original face's side detour without repeating a geometric lookup. -/
def detourRoutes {edge : OrientedEdge
  vertices.count} :
    (route : MeshPathWalks.EdgeRoute mesh edge) → MeshPathWalks.RouteSpine mesh route.detour
  | .forward location => location.detourRoutes location.kind
  | .backward location => location.reverseDetourRoutes location.kind

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine

/-- Concatenate the original retained route spines in occurrence order. -/
def append : {first last : List
  (OrientedEdge vertices.count)} →
    MeshPathWalks.RouteSpine mesh first → MeshPathWalks.RouteSpine mesh last → MeshPathWalks.RouteSpine mesh (first ++
      last)
  | _, _, .nil, last => last
  | _, _, .cons head tail, last => .cons head (tail.append last)

/-- Transport the same retained route spine across equality of its exact edge-word index. -/
def castWord {first last : List
  (OrientedEdge vertices.count)} (equal : first = last)
    (spine : MeshPathWalks.RouteSpine mesh first) : MeshPathWalks.RouteSpine mesh last := by
  cases equal
  exact spine

/-- Expand every original occurrence into its retained face-preserving side detour. -/
def detoured : {word : List
  (OrientedEdge vertices.count)} → (spine : MeshPathWalks.RouteSpine mesh word) → MeshPathWalks.RouteSpine mesh
  spine.detour
  | _, .nil => .nil
  | _, .cons head tail => head.detourRoutes.append tail.detoured

/-- Evaluate the retained occurrences without changing their geometry. -/
def values {α : Type} (value : (edge :
  OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge → α) :
    {word : List (OrientedEdge vertices.count)} → MeshPathWalks.RouteSpine mesh word → List α
  | _, .nil => []
  | _, .cons head tail => value _ head :: tail.values value

/-- Evaluating concatenated retained route spines concatenates their original value lists. -/
theorem values_append {α : Type}
  (value : (edge : OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge → α) :
    ∀ {first last : List (OrientedEdge vertices.count)} (left : MeshPathWalks.RouteSpine mesh first) (right :
      MeshPathWalks.RouteSpine mesh last),
      (left.append right).values value = left.values value ++ right.values value
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, right => congrArg (List.cons (value _ head))
    (RouteSpine.values_append value tail right)

/-- Transporting the original route-word index preserves all retained occurrence values. -/
theorem values_castWord {α : Type}
  (value : (edge : OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge → α)
    {first last : List (OrientedEdge vertices.count)} (equal : first = last) (spine : MeshPathWalks.RouteSpine mesh
      first) :
    (spine.castWord equal).values value = spine.values value := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine

end
end
end
