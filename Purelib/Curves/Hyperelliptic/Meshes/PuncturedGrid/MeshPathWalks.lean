module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Mesh.RectangleDetours
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
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
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.RootIsolation.SquareRoot.Grid.Walk

open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

open Purelib.Topology.Chain

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

public section

/-!
# Routing supported mesh words on the actual two-sheeted grid

The spine keeps one retained face, diagonal/side kind and orientation for
every original edge occurrence. Its materialized grid walk preserves both
endpoint indices' coordinates and sheets. Empty words and reversed boundary
edges are included; no connectivity search or extra closing connector occurs.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Topology.Surface.Cut.JumpPaths

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank}

set_option genInjectivity false in
/-- The retained original face location and orientation used to route one supported indexed mesh edge. -/
inductive EdgeRoute (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (edge : Stokes.OrientedEdge vertices.count)
  where
  /-- Retain the original forward supported edge occurrence and its exact lifted-face location. -/ | forward (location :
    LiftedFaces.EdgeLocation mesh.lifts edge)
  /-- Retain the original reversed supported edge occurrence and its exact lifted-face location. -/ | backward (location
    : LiftedFaces.EdgeLocation mesh.lifts edge.reverse)

constructive_injectivity EdgeRoute

namespace EdgeRoute

variable {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces} {edge :
  Purelib.Topology.Polygon.Stokes.OrientedEdge vertices.count}

/-- Locate the original supported oriented mesh edge or its reverse in the retained lifted-face bank. -/
@[expose] def build (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (edge : Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces) :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge :=
  if member : edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces then .forward (mesh.locateEdge edge member)
  else .backward (mesh.locateEdge edge.reverse (supported.resolve_left member))

/-- Read the retained original face route as a root grid walk in the requested edge orientation. -/
@[expose] def walk : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge → Vertex.VertexWalk
  vertices edges edge.start edge.finish
  | .forward location => location.walk
  | .backward location => location.walk.reverse (fun point member => (BranchCellBank.referenceAt bank point
    member).toLoop)

/-- Read the retained original rectangle detour word in the requested edge orientation. -/
@[expose] def detour : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge → List
  (Stokes.OrientedEdge vertices.count)
  | .forward location => location.lifted.quad.detour location.kind
  | .backward location => CutPath.reverse (location.lifted.quad.detour location.kind)

/-- The retained original edge route reads back exactly its indexed detour word. -/
theorem walk_indexed (route : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
  route.walk.indexed = route.detour := by
  cases route with
  | forward location => exact location.walk_indexed
  | backward location => exact congrArg CutPath.reverse location.walk_indexed

/-- Each retained original mesh-edge detour contains at most two grid sides. -/
theorem detour_length_le (route : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
  route.detour.length ≤ 2 := by
  cases route with
  | forward location => exact RectangleDetours.detour_length_le location.lifted.quad location.kind
  | backward location =>
      simpa only [Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.detour, CutPath.reverse,
        Data.List.Map.length_map, Data.List.Reverse.length_reverse] using
        RectangleDetours.detour_length_le location.lifted.quad location.kind

/-- The retained detour word preserves the exact original indexed edge endpoints. -/
theorem detour_endpoints (route : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish route.detour edge.start edge.finish := by
  cases route with
  | forward location =>
      exact ((RectangleDetours.detour_endpoints location.lifted.quad location.kind).castStart
        (congrArg OrientedEdge.start location.edge_eq)).castFinish (congrArg OrientedEdge.finish location.edge_eq)
  | backward location =>
      exact CutPath.reverse_endpoints (((RectangleDetours.detour_endpoints location.lifted.quad location.kind).castStart
        (congrArg OrientedEdge.start location.edge_eq)).castFinish (congrArg OrientedEdge.finish location.edge_eq))

/-- The retained edge detour remains supported by the original mesh triangle-edge list. -/
theorem detour_supported (route : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) route.detour := by
  rw [mesh.triangleEdges_eq]
  cases route with
  | forward location =>
      exact CutPath.supported_mono (RectangleDetours.detour_supported location.lifted.quad location.kind)
        location.retained
  | backward location =>
      exact CutPath.supported_reverse
        (CutPath.supported_mono (RectangleDetours.detour_supported location.lifted.quad location.kind)
          location.retained)

end EdgeRoute

set_option genInjectivity false in
/-- An original-order spine retaining the chosen face location and orientation of every supported mesh-edge occurrence.
-/
inductive RouteSpine (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) : List (Stokes.OrientedEdge vertices.count)
  → Type
  /-- The empty original supported mesh word has an empty retained route spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh []
  /-- Retain the original head mesh-edge route followed by the exact original word tail. -/ | cons {edge :
    Stokes.OrientedEdge vertices.count} {rest : List (Stokes.OrientedEdge vertices.count)}
      (head : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) (tail :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh rest) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh (edge :: rest)

constructive_injectivity RouteSpine

namespace RouteSpine

variable {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}

/-- Retain a face route for every original supported mesh-word occurrence in order. -/
@[expose] def build (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) : (word : List (Stokes.OrientedEdge
  vertices.count)) →
    CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) word →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word
  | [], _ => .nil
  | edge :: rest, supported => .cons (Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.build mesh edge
    (supported edge List.mem_cons_self))
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.build mesh rest (fun next member =>
        supported next (List.mem_cons_of_mem _ member)))

/-- Concatenate the retained original edge detours in their exact word order. -/
@[expose] def detour : {word : List (Stokes.OrientedEdge vertices.count)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word → List (Stokes.OrientedEdge
  vertices.count)
  | _, .nil => []
  | _, .cons head tail => head.detour ++ tail.detour

/-- An empty original indexed path has equal start and finish indices. -/
public theorem nil_endpoints {first last : Fin vertices.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish [] first last) : first = last := by
  cases path; rfl

/-- A nonempty original indexed path retains its head start and the exact endpoint path of its tail. -/
public theorem cons_endpoints {edge : Stokes.OrientedEdge vertices.count} {rest : List (Stokes.OrientedEdge
  vertices.count)}
    {first last : Fin vertices.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edge :: rest) first last) :
    edge.start = first ∧ PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish rest edge.finish last := by
  cases path with
  | cons tail => exact ⟨rfl, tail⟩

/-- Join the retained edge routes into a root grid walk preserving the original path endpoint indices. -/
@[expose] def walk : {word : List (Stokes.OrientedEdge vertices.count)} → (spine :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) →
    {first last : Fin vertices.count} → PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first
      last →
      Vertex.VertexWalk vertices edges first last
  | _, .nil, first, _, path => (VertexWalk.nil vertices edges first).castVertices rfl
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.nil_endpoints path)
  | _, .cons head tail, _, _, path =>
      (head.walk.append (tail.walk (Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.cons_endpoints
        path).2)).castVertices (Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.cons_endpoints
        path).1 rfl

/-- The complete retained root grid walk reads back the exact original-order detour word. -/
theorem walk_indexed : {word : List (Stokes.OrientedEdge vertices.count)} → (spine :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) →
    {first last : Fin vertices.count} → (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      first last) →
      (spine.walk path).indexed = spine.detour
  | _, .nil, _, _, path => by
    rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.walk, VertexWalk.castVertices_indexed]; rfl
  | _, .cons head tail, _, _, path => by
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.walk, VertexWalk.castVertices_indexed]
      change head.walk.indexed ++ (tail.walk
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.cons_endpoints path).2).indexed =
        head.detour ++ tail.detour
      rw [head.walk_indexed, tail.walk_indexed]

/-- The complete retained detour word is supported by the same original mesh triangle-edge list. -/
theorem detour_supported : {word : List (Stokes.OrientedEdge vertices.count)} → (spine :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) →
    CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) spine.detour
  | _, .nil => fun _ member => (List.not_mem_nil member).elim
  | _, .cons head tail => CutPath.supported_append head.detour_supported tail.detour_supported

/-- The complete retained detour has at most twice the original word length. -/
theorem detour_length_le : {word : List (Stokes.OrientedEdge vertices.count)} → (spine :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) →
    spine.detour.length ≤ 2 * word.length
  | _, .nil => Nat.le_refl 0
  | _, .cons head tail => by
      have first := head.detour_length_le
      have rest := tail.detour_length_le
      simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.detour,
        Data.List.Append.length_append, List.length_cons]
      omega

end RouteSpine

set_option genInjectivity false in
/-- Both words are retained: the input mesh word and its actual grid route. This does not identify integrals of diagonal
and detour paths. -/
structure RoutedPath (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (word : List (Stokes.OrientedEdge
  vertices.count))
    (first last : Fin vertices.count) where
  /-- The retained face-and-orientation route spine for the exact original mesh word. -/ spine :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word
  /-- The cached original root grid walk preserving the requested indexed endpoints. -/ walk : Vertex.VertexWalk
    vertices edges first last
  /-- The cached original grid walk reads back exactly the retained route spine's detour word. -/ indexed_eq :
    walk.indexed = spine.detour

constructive_injectivity RoutedPath

/-- The retained grid route uses at most twice the original mesh-word edge count. -/
theorem RoutedPath.edgeCount_le {mesh : GridLiftedMesh.LiftedMesh vertices edges faces} {word : List
  (Stokes.OrientedEdge vertices.count)}
    {first last : Fin vertices.count} (path : Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RoutedPath mesh
      word first last) :
    path.walk.walk.edgeCount ≤ 2 * word.length := by
  rw [← edges.indexedEdges_length vertices path.walk.walk (vertices.sheet first), ← path.walk.indexed_eq,
    path.indexed_eq]
  exact path.spine.detour_length_le

/-- Cache the original supported mesh word's route spine and corresponding endpoint-preserving root grid walk. -/
@[expose] def routePath (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (word : List (Stokes.OrientedEdge
  vertices.count))
    {first last : Fin vertices.count} (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      first last)
    (supported : CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) word) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RoutedPath mesh word first last :=
  let spine := Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.build mesh word supported
  ⟨spine, spine.walk path, spine.walk_indexed path⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
