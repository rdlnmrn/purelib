module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.RootIsolation.SquareRoot.Grid.Walk

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Assign retained grid-walk occurrences to their actual mesh faces

The executable input is the cached lifted-edge list. Its root-transported
agreement with the grid walk is used only in propositions. Assignment never
recomputes the edge bank's sheet transitions or prepares a replacement walk.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine EdgeRoute)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Topology.Surface.Cut.JumpPaths

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments

/-- The sheet is existential proof data, never a runtime instruction to replay transitions while traversing a previously
materialized word. -/
def WalkMatches {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish)
    (indexed : List (Stokes.OrientedEdge vertices.count)) : Prop :=
  ∃ sheet, indexed = edges.indexedEdges vertices walk sheet

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches

/-- A cached edge word matching the empty original grid walk is empty. -/
private theorem nil_eq {point : Data.Gaussian.Basic.Canonical} {indexed : List (Stokes.OrientedEdge vertices.count)}
    (matching : WalkFaceAssignments.WalkMatches (edges := edges) (.nil point)
      indexed) : indexed = [] := by
  obtain ⟨sheet, equal⟩ := matching
  exact equal

/-- A nonempty original grid walk cannot match an empty retained indexed word. -/
public theorem cons_not_nil {start middle finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge bank.grid start
  middle}
    {tail : Walks.Walk bank.grid middle finish}
    (matching : WalkFaceAssignments.WalkMatches (vertices := vertices) (edges
      := edges) (.cons edge tail) []) : False := by
  obtain ⟨sheet, equal⟩ := matching
  cases equal

/-- The retained head edge coordinates are exactly the original head grid edge endpoints. -/
public theorem cons_endpoints {start middle finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge bank.grid start
  middle}
    {tail : Walks.Walk bank.grid middle finish} {head : Stokes.OrientedEdge vertices.count} {rest : List
      (Stokes.OrientedEdge vertices.count)}
    (matching : WalkFaceAssignments.WalkMatches (edges := edges) (.cons edge
      tail) (head :: rest)) :
    vertices.coordinate head.start = start ∧ vertices.coordinate head.finish = middle := by
  obtain ⟨sheet, equal⟩ := matching
  change head :: rest = edges.indexedEdge vertices edge sheet :: _ at equal
  rw [(List.cons.inj equal).1]
  exact ⟨vertices.coordinate_index _ edge.vertices.1 _, vertices.coordinate_index _ edge.vertices.2 _⟩

/-- The retained word tail matches the original remaining grid walk on its actual arriving sheet. -/
public theorem cons_tail {start middle finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge bank.grid start
  middle}
    {tail : Walks.Walk bank.grid middle finish} {head : Stokes.OrientedEdge vertices.count} {rest : List
      (Stokes.OrientedEdge vertices.count)}
    (matching : WalkFaceAssignments.WalkMatches (edges := edges) (.cons edge
      tail) (head :: rest)) : WalkFaceAssignments.WalkMatches (edges := edges)
      tail rest := by
  obtain ⟨sheet, equal⟩ := matching
  exact ⟨(edges.edge edge).forward.target sheet, (List.cons.inj equal).2⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches

end

section

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces

/-- Attach already retained occurrences, including the original face on reversed detour sides. No edge lookup or root
preparation is repeated. -/
def ofRoutes (mesh : GridLiftedMesh.LiftedMesh
  vertices edges faces) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish) (indexed : List
      (Stokes.OrientedEdge vertices.count)),
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches (edges := edges) walk indexed →
        MeshPathWalks.RouteSpine mesh indexed → LiftedMesh.PathFaces mesh walk.path
  | _, _, .nil point, _, _, _ => .nil point
  | _, _, .cons _ _, [], matching, _ => matching.cons_not_nil.elim
  | _, _, .cons _edge tail, head :: rest, matching, .cons route routes =>
      .cons ⟨head, route, matching.cons_endpoints.1, matching.cons_endpoints.2⟩
        (PathFaces.ofRoutes mesh tail rest matching.cons_tail
          routes)

/-- Canonical finite lookup for clients which do not already hold a route spine. Clients with retained occurrences use
`ofRoutes` directly. -/
def ofIndexed (mesh : GridLiftedMesh.LiftedMesh
  vertices edges faces) {start finish : Data.Gaussian.Basic.Canonical}
    (walk : Walks.Walk bank.grid start finish) (indexed : List (Stokes.OrientedEdge vertices.count))
    (matching : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches (edges := edges) walk
      indexed)
    (supported : CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) indexed) :
      LiftedMesh.PathFaces mesh walk.path :=
  ofRoutes mesh walk indexed matching (RouteSpine.build mesh indexed
    supported)

/-- This is only a fold over stored indices, not root transport. -/
def indexed {ambient : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish},
      LiftedMesh.PathFaces mesh path → List (Stokes.OrientedEdge vertices.count)
  | _, _, _, .nil _ => []
  | _, _, _, .cons first tail => first.indexed :: tail.indexed

/-- Evaluate the original retained face occurrence of every segment in path order. -/
def values {α : Type} (value : (edge :
  Stokes.OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge → α)
    {ambient : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish},
      LiftedMesh.PathFaces mesh path → List α
  | _, _, _, .nil _ => []
  | _, _, _, .cons first tail => value _ first.location ::
    PathFaces.values value tail

/-- Attaching retained routes to the original grid walk preserves their exact occurrence values. -/
theorem ofRoutes_values {α : Type} (value : (edge :
  Stokes.OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge → α) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish) (word : List
      (Stokes.OrientedEdge vertices.count))
      (matching : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches (edges := edges)
        walk word)
        (routes : MeshPathWalks.RouteSpine mesh word),
      (ofRoutes mesh walk word matching routes).values value =
        routes.values value
  | _, _, .nil _, word, matching, routes => by
      have empty := matching.nil_eq
      subst word
      cases routes
      rfl
  | _, _, .cons _ _, [], matching, _ => matching.cons_not_nil.elim
  | _, _, .cons _ tail, _ :: rest, matching, .cons route routes =>
      congrArg (List.cons (value _ route)) (PathFaces.ofRoutes_values
        value tail rest matching.cons_tail routes)

/-- Attaching retained routes preserves the exact original cached indexed word. -/
theorem ofRoutes_indexed (mesh :
  GridLiftedMesh.LiftedMesh vertices edges faces) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish) (word : List
      (Stokes.OrientedEdge vertices.count))
      (matching : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches (edges := edges)
        walk word)
      (routes : MeshPathWalks.RouteSpine mesh word), (ofRoutes mesh
        walk word matching routes).indexed = word
  | _, _, .nil _, _, matching, _ => matching.nil_eq.symm
  | _, _, .cons _ _, [], matching, _ => matching.cons_not_nil.elim
  | _, _, .cons _ tail, head :: rest, matching, .cons _ routes =>
      congrArg (List.cons head) (PathFaces.ofRoutes_indexed mesh tail
        rest matching.cons_tail routes)

/-- The face assignment reads back exactly the supplied original indexed word. -/
theorem ofIndexed_indexed (mesh :
  GridLiftedMesh.LiftedMesh vertices edges faces)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish) (word : List
      (Stokes.OrientedEdge vertices.count))
    (matching : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments.WalkMatches (edges := edges) walk
      word)
    (supported : CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) word) :
    (ofIndexed mesh walk word matching supported).indexed = word :=
  ofRoutes_indexed mesh walk word matching (RouteSpine.build mesh
    word supported)

/-- There is one retained indexed edge per original path segment. -/
theorem indexed_length {ambient :
  Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      (assigned : LiftedMesh.PathFaces mesh path),
      assigned.indexed.length = path.segmentCount
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ tail => congrArg Nat.succ tail.indexed_length

/-- Attach actual mesh faces to the retained vertex walk's original cached edge word. -/
def ofVertexWalk (mesh : GridLiftedMesh.LiftedMesh
  vertices edges faces) {first last : Fin vertices.count}
    (walk : Vertex.VertexWalk vertices edges first last)
    (supported : CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) walk.indexed) :
    LiftedMesh.PathFaces mesh walk.walk.path :=
  ofIndexed mesh walk.walk walk.indexed ⟨vertices.sheet first,
    walk.indexed_eq⟩ supported

/-- The vertex-walk face assignment preserves its exact original indexed edge word. -/
theorem ofVertexWalk_indexed (mesh :
  GridLiftedMesh.LiftedMesh vertices edges faces) {first last : Fin vertices.count}
    (walk : Vertex.VertexWalk vertices edges first last)
    (supported : CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) walk.indexed) :
    (ofVertexWalk mesh walk supported).indexed = walk.indexed :=
  ofIndexed_indexed mesh walk.walk walk.indexed ⟨vertices.sheet
    first, walk.indexed_eq⟩ supported

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces

end
end
