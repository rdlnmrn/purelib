module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank RootFrames)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Reversal of the actual lifted grid paths

Reversing a walk starts on its computed final sheet and reads the cached
backward edge maps.  Its indexed list is literally the reversed list of
reversed lifted edges.  In particular, a connector and its return cancel
without an assumed same-root handoff or independent reverse preparation.
-/

section

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea_reverse edgeListArea)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {frames : RootFrames grid}

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

/-- Reverse accumulation cancels the original forward sheet transport before following the retained suffix. -/
private theorem target_reverseOnto (edges : RootEdgeBank frames)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point) :
    {start middle finish : Canonical} → (left : Walk grid start middle) → (right :
      Walk grid start finish) → (sheet : Fin 2) →
      SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges (left.reverseOnto right)
        (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges left sheet) = SquareRoot.Grid.EdgeBank.RootEdgeBank.target
        edges right sheet
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons edge tail, right, sheet => by
      change SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges (tail.reverseOnto (.cons (.reverse edge) right))
        (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges tail ((edges.edge edge).forward.target sheet)) = _
      rw [target_reverseOnto edges reference tail]
      change SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges right ((edges.edge edge).backward.target ((edges.edge
        edge).forward.target sheet)) = _
      exact congrArg (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges right)
        (((edges.edge edge).bijection (reference _ edge.vertices.1) (reference _ edge.vertices.2)).backward_forward
          sheet)

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Following the original walk and its reverse restores the initial sheet. -/
theorem target_reverse (edges :
  RootEdgeBank frames)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {start finish : Canonical} (walk : Walk grid start finish) (sheet : Fin 2) :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk.reverse (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges
      walk sheet) = sheet :=
  SquareRoot.Grid.Walk.Reversal.target_reverseOnto edges reference walk (.nil _) sheet

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

/-- Reverse accumulation gives the exact reversed indexed edge list followed by the original suffix list.

The accumulator carries the same original suffix walk and computed sheet. Its retained backward edge maps reverse each
original indexed edge and preserve that suffix list. -/
private theorem indexedEdges_reverseOnto (edges : RootEdgeBank frames) (vertices :
  VertexBank grid)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point) :
    {start middle finish : Canonical} → (left : Walk grid start middle) → (right :
      Walk grid start finish) → (sheet : Fin 2) →
      edges.indexedEdges vertices (left.reverseOnto right) (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges left
        sheet) =
        (edges.indexedEdges vertices left sheet).reverse.map Topology.Polygon.Stokes.OrientedEdge.reverse ++
          edges.indexedEdges vertices right sheet
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons edge tail, right, sheet => by
      change edges.indexedEdges vertices (tail.reverseOnto (.cons (.reverse edge) right))
        (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges tail ((edges.edge edge).forward.target sheet)) = _
      rw [indexedEdges_reverseOnto edges vertices reference tail]
      change _ ++ edges.indexedEdge vertices (.reverse edge) ((edges.edge edge).forward.target sheet) ::
        edges.indexedEdges vertices right ((edges.edge edge).backward.target ((edges.edge edge).forward.target sheet)) =
          _
      have returned : (edges.edge edge).backward.target ((edges.edge edge).forward.target sheet) = sheet :=
        ((edges.edge edge).bijection (reference _ edge.vertices.1) (reference _ edge.vertices.2)).backward_forward sheet
      rw [edges.indexedEdge_reverse vertices edge (reference _ edge.vertices.1) (reference _ edge.vertices.2), returned]
      simp only [RootEdgeBank.indexedEdges, Reverse.reverse_cons, Map.map_append,
        List.map_cons, List.map_nil,
        Append.append_assoc, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rfl

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- The indexed lift of a reversed walk is the reversed original edge list with every edge reversed.

The original reverse accumulator ends with the empty suffix. Its exact list equation therefore reads every retained edge
in reverse order and orientation. -/
theorem indexedEdges_reverse (edges :
  RootEdgeBank frames) (vertices : VertexBank grid)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {start finish : Canonical} (walk : Walk grid start finish) (sheet : Fin 2) :
    edges.indexedEdges vertices walk.reverse (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk sheet) =
      (edges.indexedEdges vertices walk sheet).reverse.map OrientedEdge.reverse := by
  rw [Walk.reverse, SquareRoot.Grid.Walk.Reversal.indexedEdges_reverseOnto edges vertices reference]
  exact Append.append_nil _

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

/-- Reversing a finite edge list and each edge negates its primitive area.

The same original finite edge list supplies every primitive endpoint value. Structural induction reverses its retained
order and applies scalar antisymmetry to each edge area. -/
private theorem reverse_edgeListArea {count : Nat} (primitive : Fin count → Topology.Polygon.Stokes.PrimitivePoint) :
    (entries : List (Topology.Polygon.Stokes.OrientedEdge count)) →
      Topology.Polygon.Stokes.edgeListArea primitive (entries.reverse.map Topology.Polygon.Stokes.OrientedEdge.reverse)
        = -Topology.Polygon.Stokes.edgeListArea primitive entries
  | [] => by change (0 : Canonical) = -0; ring1
  | edge :: tail => by
      rw [Reverse.reverse_cons, Map.map_append, Topology.Polygon.Stokes.edgeListArea_append,
        reverse_edgeListArea primitive tail]
      change -Topology.Polygon.Stokes.edgeListArea primitive tail + (Topology.Polygon.Stokes.edgeArea (primitive
        edge.finish) (primitive edge.start) + 0) =
        -(Topology.Polygon.Stokes.edgeArea (primitive edge.start) (primitive edge.finish) +
          Topology.Polygon.Stokes.edgeListArea primitive tail)
      rw [Topology.Polygon.Stokes.edgeArea_reverse (primitive edge.finish) (primitive edge.start)]
      ring1

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Reversing the original indexed lifted walk negates its primitive edge-list area. -/
theorem indexedEdges_reverse_area (edges :
  RootEdgeBank frames) (vertices : VertexBank grid)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (primitive : Fin vertices.count → Topology.Polygon.Stokes.PrimitivePoint) {start finish : Canonical}
      (walk : Walk grid start finish) (sheet : Fin 2) :
    Topology.Polygon.Stokes.edgeListArea primitive (edges.indexedEdges vertices walk.reverse
      (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk sheet)) =
      -Topology.Polygon.Stokes.edgeListArea primitive (edges.indexedEdges vertices walk sheet) := by
  rw [edges.indexedEdges_reverse vertices reference]
  exact Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal.reverse_edgeListArea primitive _

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end
