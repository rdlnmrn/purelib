module
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex (VertexWalk)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-!
# Operational preparation of closed lifted vertex walks

Return of the shared edge-bank transport gives a closed rational root trace,
hence even winding. That proof is erased: preparing the integration path
does not execute the auxiliary root readings used to prove divisibility.
The actual prepared owner thread then returns operationally by monodromy.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName OwnerJoin)
open Purelib.Riemann.RootContinuation.SquareRootTrace (WindingComparison)

open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid}
    {edges : SquareRoot.Grid.RootEdgeBank frames} {index : Fin vertices.count}

/-- Divisibility follows from the actual closed owner trace, not from a
supplied parity bit or a topological name for the cycle. -/
theorem winding_even (path :
  VertexWalk vertices edges index index) :
    (Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding path.walk.path) = 8 *
      ((Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding path.walk.path) / 8) := open
      Purelib.Approximation.Gaussian in by
  let member := vertices.coordinate_onGrid index
  let actual := SquareRoot.Grid.EdgeBank.RootEdgeBank.trace edges path.walk member member (vertices.sheet index)
  have returned : Equivalence.NamedEquivalent
      (ownerName ((frames.frameAt _ member).owners (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges path.walk
        (vertices.sheet index))))
      (ownerName (vertices.owner frames index)) := by
    rw [path.sheet_eq]
    exact Equivalence.NamedEquivalent.refl _
  let closed := actual.close (OwnerJoin.acquire _ _ returned)
  have multiple := (WindingComparison.build closed.trace).raw_eq
  rw [Riemann.Paths.PreparedPathClosure.SquareRootTrace.OwnerPath.closedRaw_eq_chainRaw actual] at multiple
  have winding := SquareRoot.Grid.EdgeBank.RootEdgeBank.trace_winding edges path.walk member member (vertices.sheet
    index)
  have equal := winding.symm.trans multiple
  omega

/-- Reuse any retained or generated preparation with checked trace and
primitive coverage. No equality to the canonical preparation is required. -/
def rootClosedOfCovered (path :
  VertexWalk vertices edges index index)
    (reference : WindingOneLoop polynomial (vertices.coordinate index))
    (covered : CoveredTracedPath path.walk.path (vertices.owner frames index)) :
    RootClosedWalk grid (vertices.coordinate index) (vertices.owner frames index) :=
  ⟨path.walk, covered.traced, covered.cover, ownerName (vertices.owner frames index),
    ownerName covered.traced.finishOwner, rfl, rfl,
    Riemann.Paths.OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference covered.traced.trace.get
      ((Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding path.walk.path) / 8)
      ((Riemann.Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original covered.traced).trans
        path.winding_even)⟩

/-- Construct the retained closed root trace of an actual closed lifted grid walk.

The canonical covered trace supplies the primitive-cover evidence on the original indexed edge word. -/
def rootClosed (path :
  VertexWalk vertices edges index index)
    (reference : WindingOneLoop polynomial (vertices.coordinate index)) :
    RootClosedWalk grid (vertices.coordinate index) (vertices.owner frames index) :=
  path.rootClosedOfCovered reference (CoveredTracedPath.build path.walk.path path.walk.withinAmbient (vertices.owner
    frames index))

/-- The constructed closed root trace retains the exact original grid walk. -/
theorem rootClosed_walk (path :
  VertexWalk vertices edges index index)
    (reference : WindingOneLoop polynomial (vertices.coordinate index)) :
    (path.rootClosed reference).walk = path.walk := rfl

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk
