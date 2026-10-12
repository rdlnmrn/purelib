module
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
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Sum.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Two-sheet boundary values from the actual shared root transports

The two lifts of a walk may exchange their sheet labels at every edge.
Summing both lifts removes that reindexing, because each checked edge map is
a bijection.  A materialized table of positive-edge areas therefore supplies
the existing base-grid cancellation interface even for sheet-dependent
primitive values.  Reverse edges consume the same cached transports.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues)

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {frames : RootFrames grid}

namespace Boundary.Values

/-- Read the first cached area for an ordered endpoint pair, returning zero when absent. -/
@[expose] def lookupArea (key : Canonical × Canonical) : List ((Canonical ×
  Canonical) × Canonical) → Canonical
  | [] => 0
  | head :: tail => if key = head.1 then head.2 else
    lookupArea key tail

end Boundary.Values

section RootEdgeEntry

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.RootEdgeEntry (key lookup)

namespace Boundary.Values.RootEdgeEntry

/-- Sum the primitive edge areas along both retained sheet connections.

The sum uses both original sheet indices and the target indices retained by the same root-edge connection. -/
@[expose] def connectionArea (vertices : VertexBank grid) (primitive : Fin vertices.count
  → PrimitivePoint)
    (start finish : Canonical) (first : ContainsVertex grid start)
      (last :
      ContainsVertex grid finish)
    (connection : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt
      finish last)) : Canonical :=
  Topology.Polygon.Stokes.edgeArea (primitive (vertices.index start first 0))
      (primitive (vertices.index finish last (connection.forward.target 0))) +
    Topology.Polygon.Stokes.edgeArea (primitive (vertices.index start first 1))
      (primitive (vertices.index finish last (connection.forward.target 1)))

end Boundary.Values.RootEdgeEntry

namespace RootEdgeBank.RootEdgeEntry

/-- Read the two-sheet primitive area of this retained root-edge entry. -/
@[expose] def liftedArea (vertices :
  VertexBank grid) (primitive : Fin vertices.count →
  PrimitivePoint)
    (entry : SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames) : Canonical :=
  Boundary.Values.RootEdgeEntry.connectionArea vertices primitive entry.start entry.finish
    entry.first entry.last entry.connection

end RootEdgeBank.RootEdgeEntry

namespace Boundary.Values.RootEdgeEntry

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.RootEdgeEntry in
/-- Looking up the mapped area table reads the exact retained root-edge connection selected by the original endpoint
lookup. -/
private theorem lookupArea_map (vertices : VertexBank grid) (primitive : Fin
  vertices.count → PrimitivePoint)
    (start finish : Canonical) (first : ContainsVertex grid start)
      (last :
      ContainsVertex grid finish) :
    (entries : List (SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames)) → (member : (start, finish) ∈ entries.map key)
      →
      lookupArea (start, finish) (entries.map fun entry => (entry.key,
        entry.liftedArea vertices primitive)) =
        connectionArea vertices primitive start finish first last
          (SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.lookup frames start finish first last entries member)
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member => by
      rw [SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.lookup]
      split
      next equal =>
        simp only [List.map_cons, lookupArea, if_pos equal]
        have startEq : start = head.start := congrArg Prod.fst equal
        have finishEq : finish = head.finish := congrArg Prod.snd equal
        cases startEq
        cases finishEq
        rfl
      next equal =>
        simp only [List.map_cons, lookupArea, if_neg equal]
        exact lookupArea_map vertices primitive
          start finish first last tail _

end Boundary.Values.RootEdgeEntry

end RootEdgeEntry

namespace RootEdgeBank

/-- Sum the primitive areas of the two actual indexed lifts of one original grid edge. -/
@[expose] def twoSheetEdgeArea (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) {start finish : Canonical}
      (edge : Edge grid start finish) : Canonical :=
  let zero := edges.indexedEdge vertices edge 0
  let one := edges.indexedEdge vertices edge 1
  Topology.Polygon.Stokes.edgeArea (primitive zero.start) (primitive zero.finish) + Topology.Polygon.Stokes.edgeArea
    (primitive one.start) (primitive one.finish)

/-- Sum the primitive edge-list areas of both actual lifts of the original grid walk. -/
@[expose] def twoSheetArea (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) {start finish : Canonical}
      (walk : Geometry.Grid.Walks.Walk grid start finish) : Canonical :=
  Topology.Polygon.Stokes.edgeListArea primitive (edges.indexedEdges vertices walk 0) +
    Topology.Polygon.Stokes.edgeListArea primitive (edges.indexedEdges vertices walk 1)

/-- Compute each positive-edge area once for this primitive assignment;
the horizontal and vertical readbacks only scan the retained value table. -/
@[expose] def edgeValues (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) : EdgeValues :=
  let table := edges.entries.map fun entry => (entry.key, entry.liftedArea vertices primitive)
  { horizontal := fun first last y => Boundary.Values.lookupArea (Gaussian.Components.Basic.point
    first y, Gaussian.Components.Basic.point last y) table
    vertical := fun x first last => Boundary.Values.lookupArea (Gaussian.Components.Basic.point x
      first, Gaussian.Components.Basic.point x last) table }

/-- Both sheet sums negate on reversal; the inverse map may swap their
order, so proving only two separate endpoint equations is insufficient. -/
theorem twoSheetEdgeArea_reverse (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) {start finish : Canonical}
      (edge : Edge grid start finish)
    (first : WindingOneLoop polynomial start) (last :
      WindingOneLoop polynomial finish) :
    edges.twoSheetEdgeArea vertices primitive (.reverse edge) = -edges.twoSheetEdgeArea vertices primitive edge := by
  let area := fun sheet =>
    let lifted := edges.indexedEdge vertices (.reverse edge) sheet
    Topology.Polygon.Stokes.edgeArea (primitive lifted.start) (primitive lifted.finish)
  have reindex := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (edges.edge edge).forward.target
    ((edges.edge edge).bijection first last).forward_injective area
  change area 0 + area 1 = _
  rw [← reindex]
  simp only [area, edges.indexedEdge_reverse vertices edge first last,
    Topology.Polygon.Stokes.OrientedEdge.reverse, twoSheetEdgeArea]
  rw [Topology.Polygon.Stokes.edgeArea_reverse (primitive (edges.indexedEdge vertices edge 0).finish)
      (primitive (edges.indexedEdge vertices edge 0).start),
    Topology.Polygon.Stokes.edgeArea_reverse (primitive (edges.indexedEdge vertices edge 1).finish)
      (primitive (edges.indexedEdge vertices edge 1).start)]
  ring1

/-- The cached edge-value table agrees with the two-sheet area of every original grid edge. -/
theorem edgeValues_edge (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point) :
    {start finish : Canonical} → (edge : Edge grid start finish) →
      (edges.edgeValues vertices primitive).edge edge = edges.twoSheetEdgeArea vertices primitive edge
  | _, _, .horizontal interval adjacent line member =>
      Boundary.Values.RootEdgeEntry.lookupArea_map vertices primitive _ _ _ _ edges.entries
        (edges.horizontal interval adjacent line member)
  | _, _, .vertical interval adjacent line member =>
      Boundary.Values.RootEdgeEntry.lookupArea_map vertices primitive _ _ _ _ edges.entries
        (edges.vertical interval adjacent line member)
  | start, finish, .reverse original => by
      change -(edges.edgeValues vertices primitive).edge original = _
      rw [edges.edgeValues_edge vertices primitive reference original,
        edges.twoSheetEdgeArea_reverse vertices primitive original
          (reference finish original.vertices.1) (reference start original.vertices.2)]

/-- The cached walk-value sum agrees with the areas of both retained lifted walks. -/
theorem edgeValues_walk (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point) :
    {start finish : Canonical} → (walk : Geometry.Grid.Walks.Walk grid start finish) →
      (edges.edgeValues vertices primitive).walk walk = edges.twoSheetArea vertices primitive walk
  | _, _, .nil _ => by change (0 : Canonical) = 0 + 0; ring1
  | _, _, .cons edge tail => by
      change (edges.edgeValues vertices primitive).edge edge + (edges.edgeValues vertices primitive).walk tail = _
      rw [edges.edgeValues_edge vertices primitive reference edge, edges.edgeValues_walk vertices primitive reference
        tail]
      have reindex := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (edges.edge edge).forward.target
        ((edges.edge edge).bijection (reference _ edge.vertices.1) (reference _ edge.vertices.2)).forward_injective
        (fun sheet => Topology.Polygon.Stokes.edgeListArea primitive (edges.indexedEdges vertices tail sheet))
      simp only [twoSheetArea,
        SquareRoot.Grid.RootEdgeBank.indexedEdges, Topology.Polygon.Stokes.edgeListArea,
        twoSheetEdgeArea]
      rw [← reindex]
      ring1

end RootEdgeBank
end Grid

end Purelib.RootIsolation.SquareRoot.Grid
