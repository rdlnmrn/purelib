module
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.RootIsolation.SquareRoot.Grid.RootEdges

@[expose] public section

/-! Reassemble the original two-sheet transports from restored traced paths.
Endpoint classification remains the frame's canonical classifier. -/
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
namespace Purelib.Riemann.RootContinuation.RootTransportReplay

open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow PathTransport)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdges (RootEdge)

variable {p : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {box :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}

section
open Purelib.Polynomial
/-- Reassemble one original sheet transport from its restored trace and endpoint selection. -/
def row (path : Polynomial.Geometry.ClearPath p box start finish)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish)) (index : Fin 2)
    (traced : TracedPath path (first.owners index))
    (selected : OwnerSelection last.owners traced.finishOwner) : TransportRow path first last index :=
  ⟨traced, selected⟩

/-- Exact original trace and selector equations identify the reconstructed transport row with the original builder. -/
theorem row_eq (path : Polynomial.Geometry.ClearPath p box start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish)) (index : Fin 2)
    (traced : TracedPath path (first.owners index))
    (same : traced = TracedPath.build path within (first.owners index))
    (selected : OwnerSelection last.owners traced.finishOwner) (selectedEq : selected = last.select traced.finishOwner)
      :
    row path first last index traced selected = TransportRow.build path within first last index := by
  cases selectedEq
  cases same
  rfl

/-- Reassemble the original two-sheet path transport from its retained zero and one rows. -/
def transport (path : Polynomial.Geometry.ClearPath p box start finish)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish))
    (zero : TransportRow path first last 0) (one : TransportRow path first last 1) :
    PathTransport path first last := ⟨zero, one⟩

/-- Two exact original row readbacks identify the complete reconstructed path transport. -/
theorem transport_eq (path : Polynomial.Geometry.ClearPath p box start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish))
    (zero : TransportRow path first last 0) (one : TransportRow path first last 1)
    (zeroEq : zero = TransportRow.build path within first last 0)
    (oneEq : one = TransportRow.build path within first last 1) :
    transport path first last zero one = PathTransport.build path within first last := by
  cases zeroEq
  cases oneEq
  rfl

end

open Purelib.Curves
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Reassemble a root edge from the original segment and its retained forward and reverse path transports. -/
def edge (segment : Geometry.ClearPath.ClearSegment p box start finish)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish))
    (forward : PathTransport (.cons segment (.nil finish)) first last)
    (backward : PathTransport (.cons (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse segment) (.nil start))
      last first) :
    SquareRoot.Grid.RootEdges.RootEdge (ambient := box) first last :=
  ⟨segment, Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse segment, forward, backward⟩

/-- Exact original forward and reverse transport readbacks identify the reconstructed root edge with its original
builder. -/
theorem edge_eq (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish))
    (forward : PathTransport (.cons segment (.nil finish)) first last)
    (backward : PathTransport (.cons (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse segment) (.nil start))
      last first)
    (forwardEq : forward = PathTransport.build (.cons segment (.nil finish)) (.cons within (.nil finish)) first last)
    (backwardEq : backward = PathTransport.build (.cons (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse
      segment) (.nil start))
      (.cons (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient segment within) (.nil start))
        last first) :
    edge segment first last forward backward = SquareRoot.Grid.RootEdges.RootEdge.build segment within first last := by
  cases forwardEq
  cases backwardEq
  rfl

end Purelib.Riemann.RootContinuation.RootTransportReplay
