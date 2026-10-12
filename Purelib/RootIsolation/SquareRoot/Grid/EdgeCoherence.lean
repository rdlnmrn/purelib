module
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Topology.Polygon.Stokes

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-!
# Endpoint coherence of cached affine root transports

Independently certified clear affine segments with the same endpoints have
the same two-sheet map. The proof uses their zero-winding round trip and the
already proved inverse law. It is erased: no transport, owner or trace is
recomputed when reading or comparing retained mesh edges.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start finish :
  Gaussian.Basic.Canonical}

namespace RootEdges.RootEdge

variable {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)}

/-- Two clear root-edge connections with the same retained endpoint frames send each sheet to the same target sheet. -/
theorem forward_target_eq (left right :
  SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last)
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (sheet : Fin 2) : left.forward.target sheet = right.forward.target sheet := by
  have cancellation : Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Polynomial.Geometry.ClearPath.cons
    left.forwardSegment (.nil finish)) +
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Polynomial.Geometry.ClearPath.cons right.backwardSegment
        (.nil start)) = 0 := by
    have reversed := Riemann.Paths.PreparedPathClosure.ClearSegment.rawWinding_reverse left.forwardSegment
    change Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding right.backwardSegment =
      -Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding left.forwardSegment at reversed
    change (Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding left.forwardSegment + 0) +
      (Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding right.backwardSegment + 0) = 0
    rw [reversed]
    omega
  have returned := Riemann.RootContinuation.RootPathTransport.PathTransport.roundTrip_index firstReference left.forward
    right.backward cancellation sheet
  have restored := (right.bijection firstReference lastReference).forward_backward (left.forward.target sheet)
  exact restored.symm.trans (congrArg right.forward.target returned)

end RootEdges.RootEdge

namespace RootEdgeBank

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {frames :
  RootIsolation.SquareRoot.Grid.RootFrames
    grid}

/-- Root-edge descriptions with the same endpoints produce the same indexed lift for each original sheet. -/
theorem indexedEdge_eq (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (left right : Edge grid start finish) (firstReference : WindingOneLoop polynomial start)
    (lastReference : WindingOneLoop polynomial finish) (sheet : Fin 2) :
    edges.indexedEdge vertices left sheet = edges.indexedEdge vertices right sheet :=
  congrArg (fun target => (⟨vertices.index start left.vertices.1 sheet,
    vertices.index finish left.vertices.2 target⟩ : Topology.Polygon.Stokes.OrientedEdge vertices.count))
      ((edges.edge left).forward_target_eq (edges.edge right) firstReference lastReference sheet)

/-- A neighboring cell may use different clearance payloads for the reverse
side. Its actual lifted indices still reverse the original edge exactly. -/
theorem indexedEdge_opposite (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    (left : Edge grid start finish) (right : Edge grid finish start)
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (sheet : Fin 2) :
    edges.indexedEdge vertices right ((edges.edge left).forward.target sheet) =
      (edges.indexedEdge vertices left sheet).reverse :=
  (edges.indexedEdge_eq vertices right (.reverse left) lastReference firstReference _).trans
    (edges.indexedEdge_reverse vertices left firstReference lastReference sheet)

/-- Endpoint-identical opposite grid edges give exactly reversed indexed lifts on the transported sheet. -/
theorem indexedEdge_opposite_of_endpoints (edges
  : SquareRoot.Grid.RootEdgeBank frames) (vertices : VertexBank grid)
    {otherStart otherFinish : Gaussian.Basic.Canonical} (left : Edge grid start finish) (right :
      Edge grid otherStart otherFinish)
    (startEq : otherStart = finish) (finishEq : otherFinish = start)
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (sheet : Fin 2) :
    edges.indexedEdge vertices right ((edges.edge left).forward.target sheet) =
      (edges.indexedEdge vertices left sheet).reverse := by
  cases startEq
  cases finishEq
  exact edges.indexedEdge_opposite vertices left right firstReference lastReference sheet

end RootEdgeBank

end Purelib.RootIsolation.SquareRoot.Grid
