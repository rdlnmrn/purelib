module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootOwnerFrames
public import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Reversible actual root transports on grid edges

Each direction retains its prepared single-segment path and the checked
classification of both finish owners in the shared endpoint frame.  Swapping
directions reuses these rows.  The inverse laws follow from actual
zero-winding round trips, without an assumed matching or injectivity proof.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdges

open Purelib
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start finish :
  Gaussian.Basic.Canonical}

set_option genInjectivity false in
/-- A reversible root edge retains clear segments and prepared transports in both directions.

Both transports use the supplied endpoint frames and their exact affine
segments. The reverse direction has its own retained clearance and stored rows. -/
structure RootEdge (first : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval start)) (last :
  Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval finish)) where
  /-- The retained clear affine segment from the first endpoint to the last. -/ forwardSegment :
    Geometry.ClearPath.ClearSegment polynomial ambient start finish
  /-- The retained clear affine segment from the last endpoint to the first. -/ backwardSegment :
    Geometry.ClearPath.ClearSegment polynomial ambient finish start
  /-- The actual prepared forward transport between the retained endpoint root frames. -/ forward :
    Riemann.RootContinuation.RootPathTransport.PathTransport (.cons forwardSegment (.nil finish)) first last
  /-- The actual prepared backward transport between the same endpoint frames. -/ backward :
    Riemann.RootContinuation.RootPathTransport.PathTransport (.cons backwardSegment (.nil start)) last first

constructive_injectivity RootEdge

namespace RootEdge

variable {first : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval start)} {last :
  Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval finish)}

open Purelib.RootIsolation.SquareRoot.Grid.RootEdges.RootEdge in
/-- Prepare both directions of one clear segment using the existing endpoint root frames.

Both resulting transports retain their actual preparations and classification rows; the reverse segment is the original
segment with reversed endpoints. -/
@[expose] def build (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within :
  segment.WithinAmbient)
    (first : Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval start)) (last :
      Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval finish)) :
    SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last :=
  let reverse := Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse segment
  { forwardSegment := segment
    backwardSegment := reverse
    forward := Riemann.RootContinuation.RootPathTransport.PathTransport.build (.cons segment (.nil finish)) (.cons
      within (.nil finish)) first last
    backward := Riemann.RootContinuation.RootPathTransport.PathTransport.build (.cons reverse (.nil start))
      (.cons (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient segment within) (.nil
        start)) last first }

/-- A reversed edge reads the stored reverse preparations, not a new run of
the continuation algorithm. -/
@[expose] def reverse (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) :
  SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) last first :=
  ⟨edge.backwardSegment, edge.forwardSegment, edge.backward, edge.forward⟩

/-- The forward and backward single-segment paths have cancelling raw windings. -/
theorem winding_cancel (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Polynomial.Geometry.ClearPath.cons edge.forwardSegment (.nil
      finish)) +
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Polynomial.Geometry.ClearPath.cons edge.backwardSegment
        (.nil start)) = 0 := by
  have reversed := Riemann.Paths.PreparedPathClosure.ClearSegment.rawWinding_reverse edge.forwardSegment
  change Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.backwardSegment =
    -Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.forwardSegment at reversed
  change (Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.forwardSegment + 0) +
    (Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.backwardSegment + 0) = 0
  rw [reversed]
  omega

/-- Construct the two-sheet bijection from the retained edge transports and endpoint winding-one references. -/
@[expose] def bijection (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last)
    (firstReference : Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial start) (lastReference :
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial finish) :
    Data.Fin.Bijection 2 2 :=
  edge.forward.bijection firstReference lastReference edge.backward edge.winding_cancel

/-- Reversing an edge reads the stored backward transport's target index. -/
theorem reverse_target (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) (index : Fin 2) :
    edge.reverse.forward.target index = edge.backward.target index := rfl

/-- Reversing an edge twice restores the original forward target index. -/
theorem reverse_reverse_target (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) (index : Fin
  2) :
    edge.reverse.reverse.forward.target index = edge.forward.target index := rfl

/-- Read the joined owner path for a displayed initial sheet from the retained forward transport row. -/
@[expose] def trace (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) (index : Fin 2) :
    Riemann.Paths.OwnerTracePath.OwnerPath polynomial start (first.owners index) finish (last.owners
      (edge.forward.target index)) :=
  (edge.forward.row index).joined

/-- The joined trace follows this exact affine edge, with only proved
same-root stationary handoffs at the endpoint. -/
theorem trace_winding (edge : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) (index : Fin 2) :
    Winding.Polygon.Basic.chainRaw polynomial start (edge.trace index).vertices =
      (Dense.Gaussian.Path.Segment.segment polynomial start finish).doubledWinding :=
  (edge.forward.row index).joined_winding.trans (Int.add_zero _)

end RootEdge

namespace RootFrames

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

open Purelib.RootIsolation.SquareRoot.Grid.RootEdges.RootFrames in
/-- Prepare a grid edge using its original endpoints in the retained frame bank.

The endpoint membership witnesses select those exact cached frames.
Both directed transports and clear segments belong to that same grid edge. -/
@[expose] def edge (frames : RootFrames grid) (edge : Geometry.Grid.Walks.Edge grid start
  finish) :
    SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start edge.vertices.1) (frames.frameAt
      finish edge.vertices.2) :=
  SquareRoot.Grid.RootEdges.RootEdge.build edge.segment edge.withinAmbient (frames.frameAt start edge.vertices.1)
    (frames.frameAt finish edge.vertices.2)

end RootFrames

end Purelib.RootIsolation.SquareRoot.Grid.RootEdges
