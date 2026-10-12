module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Meshes.GridLiftedConnections
public import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank RootFrames)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Root-transported grid walks indexed by actual mesh vertices

Coordinates and sheets are read from the retained vertex bank. Every walk
caches its literal lifted grid-edge list. Concatenation and reversal use the
existing shared transport maps and preserve that indexed list exactly.
-/

section

open Purelib.Topology.Polygon.Stokes

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
  {frames : RootFrames grid}

section

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Transporting endpoint equalities preserves the original cached target sheet. -/
theorem target_castEndpoints (edges :
  RootEdgeBank frames) {start finish first last : Canonical}
    (walk : Walk grid start finish) (startEq : start = first) (finishEq : finish = last) (sheet :
      Fin 2) :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges (walk.castEndpoints startEq finishEq) sheet =
      SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk sheet := by
  cases startEq; cases finishEq; rfl

/-- Transporting endpoint equalities preserves the exact original indexed edge list. -/
theorem indexedEdges_castEndpoints (edges :
  RootEdgeBank frames) (vertices : VertexBank grid)
    {start finish first last : Canonical} (walk : Walk grid start finish)
    (startEq : start = first) (finishEq : finish = last) (sheet : Fin 2) :
    edges.indexedEdges vertices (walk.castEndpoints startEq finishEq) sheet = edges.indexedEdges vertices walk sheet :=
      by
  cases startEq; cases finishEq; rfl

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

set_option genInjectivity false in
/-- A retained lifted grid walk indexed by its actual starting and finishing vertices.

The original coordinate walk and transported sheet determine the cached indexed edge list exactly. -/
structure VertexWalk (vertices : VertexBank grid) (edges :
  RootEdgeBank frames) (first last : Fin vertices.count) where
  /-- The actual grid walk between the original endpoint coordinates. -/ walk : Walk grid
    (vertices.coordinate first) (vertices.coordinate last)
  /-- The original walk transports the starting vertex's sheet to the finishing vertex's sheet. -/ sheet_eq :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk (vertices.sheet first) = vertices.sheet last
  /-- The retained finite indexed edge list of this lifted walk. -/ indexed : List (Topology.Polygon.Stokes.OrientedEdge
    vertices.count)
  /-- The cached list equals the original edge-bank lift on the starting vertex's sheet. -/ indexed_eq : indexed =
    edges.indexedEdges vertices walk (vertices.sheet first)

constructive_injectivity VertexWalk

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

section

variable {vertices : VertexBank grid} {edges : RootEdgeBank
  frames} {first middle last : Fin vertices.count}

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

/-- The empty retained walk at one original lifted vertex. -/
@[expose] def nil (vertices : VertexBank grid) (edges :
  RootEdgeBank frames) (index : Fin vertices.count) :
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges index index :=
  ⟨.nil _, rfl, [], rfl⟩

/-- Reindex an original lifted walk by specified vertices with matching coordinates and sheets.

The cached edge list is retained from the original path and transported using only the supplied endpoint equalities. -/
@[expose] def ofLifted {start finish : Canonical} {firstSheet lastSheet : Fin 2}
    (path : SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish lastSheet)
    (first last : Fin vertices.count) (firstCoordinate : vertices.coordinate first = start)
    (lastCoordinate : vertices.coordinate last = finish)
    (firstSheet_eq : vertices.sheet first = firstSheet) (lastSheet_eq : vertices.sheet last = lastSheet) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last :=
  { walk := path.walk.castEndpoints firstCoordinate.symm lastCoordinate.symm
    sheet_eq := by rw [edges.target_castEndpoints, firstSheet_eq, lastSheet_eq]; exact path.sheet_eq
    indexed := edges.indexedEdges vertices path.walk firstSheet
    indexed_eq := by rw [edges.indexedEdges_castEndpoints, firstSheet_eq] }

/-- Retain one original grid edge as a walk between its actual indexed lifted vertices. -/
@[expose] def ofEdge (vertices : VertexBank grid) (edges :
  RootEdgeBank frames) {start finish : Canonical}
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges (edges.indexedEdge vertices edge sheet).start
      (edges.indexedEdge vertices edge sheet).finish :=
  SquareRoot.Grid.Walk.Vertex.VertexWalk.ofLifted (⟨.cons edge (.nil _), edge.vertices.1, edge.vertices.2, rfl⟩ :
    SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start sheet finish ((edges.edge edge).forward.target
      sheet)) _ _
      (vertices.coordinate_index _ edge.vertices.1 _) (vertices.coordinate_index _ edge.vertices.2 _)
      (vertices.sheet_index _ edge.vertices.1 _) (vertices.sheet_index _ edge.vertices.2 _)

/-- The retained one-edge walk caches exactly the original indexed lifted edge. -/
theorem ofEdge_indexed (vertices : VertexBank grid) (edges :
  RootEdgeBank frames) {start finish : Canonical}
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    (SquareRoot.Grid.Walk.Vertex.VertexWalk.ofEdge vertices edges edge sheet).indexed = [edges.indexedEdge vertices edge
      sheet] := rfl

/-- Transport a retained vertex walk along equalities of its original endpoint indices. -/
@[expose] def castVertices (path : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last) {newFirst newLast :
  Fin vertices.count}
    (firstEq : first = newFirst) (lastEq : last = newLast) : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges
      newFirst newLast := by
  cases firstEq; cases lastEq; exact path

/-- Endpoint-index transport preserves the original cached edge list. -/
theorem castVertices_indexed (path : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last) {newFirst newLast
  : Fin vertices.count}
    (firstEq : first = newFirst) (lastEq : last = newLast) :
    (path.castVertices firstEq lastEq).indexed = path.indexed := by
  cases firstEq; cases lastEq; rfl

/-- Join compatible retained vertex walks and append their cached indexed edge lists. -/
@[expose] def append (left : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first middle) (right :
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges middle last) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last :=
  { walk := left.walk.append right.walk
    sheet_eq := by rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges, left.sheet_eq, right.sheet_eq]
    indexed := left.indexed ++ right.indexed
    indexed_eq := by rw [edges.indexedEdges_append, left.sheet_eq, left.indexed_eq, right.indexed_eq] }

/-- Reverse the original vertex walk, its transported sheet and its cached oriented edge word. -/
@[expose] def reverse (path : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges last first :=
  { walk := path.walk.reverse
    sheet_eq := by rw [← path.sheet_eq]; exact edges.target_reverse reference path.walk _
    indexed := Topology.Surface.Cut.JumpPaths.CutPath.reverse path.indexed
    indexed_eq := by
      rw [← path.sheet_eq, edges.indexedEdges_reverse vertices reference, path.indexed_eq]
      rfl }

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

end
end
