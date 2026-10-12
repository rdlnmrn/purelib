module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay
public import Purelib.Riemann.Integration.PreparedConstantModels

@[expose] public section

/-!
# Prepared-edge reconstruction from a checked source choice

This boundary consumes a reconstructed segment and incoming owner.  It builds
the prepared edge, including its movement certificate, without canonical
preparation.  The edge agrees with any original edge with the same inputs;
in particular, cached owner functions are identified by canonical equations,
not by comparing root-box coordinates.
-/

namespace Purelib.Riemann.Transport.PreparedEdgeReplay

open Purelib.Riemann.Branches

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
variable {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
variable {ambient : Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Box} {start finish :
  Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Gaussian}
variable (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
variable (within : segment.WithinAmbient) (current :
  Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Endpoint)
variable (source : Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Owner (curve.polynomial.eval
  (segment.pointAt current.parameter)))
variable (request : PreparedSheetContinuation.StepRequest)
variable (ordered : current.parameter ≤ request.endpoint.parameter) (sheet : Fin 2)

section
open Purelib.RootIsolation.SquareRoot.Replay
/-- Assemble the exact prepared edge from an accepted replayed source cache.

The original segment, incoming owner, request and sheet are retained. The cached movement and clearance equations supply
the original smallness certificate. -/
def ofAccepted (result : PreparedSourceReplay.Accepted segment current source request) : PreparedEdge curve differential
  :=
    { ambient := ambient, start := start, finish := finish, segment := segment,
      within := within, left := current, owner := source, request := request,
      cached := result.cached, ordered := ordered, sheet := sheet,
      small := by
        rw [← result.cached.preparedOwner_eq, ← result.movement_eq, ← result.clearance_eq]
        exact result.carries }

/-- Replay a saved source hint and assemble its accepted prepared edge.

An inconclusive source replay retains its actual indexed attempt; success reuses the accepted cache with the original
edge inputs. -/
def replay (hint : PreparedSourceReplay.Hint) :
    Except (PreparedSourceReplay.Inconclusive segment current source request hint) (PreparedEdge curve differential) :=
  (PreparedSourceReplay.replay segment current source request hint).map
    (ofAccepted segment within current source request ordered sheet)

/-- Assemble a prepared edge from a checked raw reconstruction of the original source state.

The supplied incoming owner remains the edge owner, while the reconstructed diameter-preparation cache supplies the
exact accepted source. -/
def replayRaw
    (restored : PreparedRawStateReplay.Checked _ source.ambient
      (PreparedRawStateReplay.capture source.track.initial)) :
    Except (PreparedRawSourceReplay.Inconclusive segment current source request restored)
      (PreparedEdge curve differential) :=
  (PreparedRawSourceReplay.replay segment current source request restored rfl).map
    (ofAccepted segment within current source request ordered sheet)

end

/-- Replacing an edge cache by a checked cache preserves the complete original edge.

The two cache identities are transported through their canonical equations without evaluating preparation. -/
theorem replaceCache_eq (edge : PreparedEdge curve differential)
    (cached : PreparedSheetContinuation.CachedSource edge.segment edge.left edge.owner edge.request) :
    { edge with cached := cached } = edge := by
  have equal : cached = edge.cached :=
    cached.eq_canonical.trans edge.cached.eq_canonical.symm
  cases equal
  rfl

open Purelib.RootIsolation.SquareRoot.Replay
/-- A successful source-hint replay returns the exact original prepared edge. -/
theorem replay_eq_original (edge : PreparedEdge curve differential) (hint : PreparedSourceReplay.Hint)
    (restored : PreparedEdge curve differential)
    (success : replay edge.segment edge.within edge.left edge.owner edge.request
      edge.ordered edge.sheet hint = .ok restored) : restored = edge := by
  unfold replay at success
  cases choice : PreparedSourceReplay.replay edge.segment edge.left edge.owner edge.request hint with
  | error failed => simp only [choice, Except.map] at success; cases success
  | ok result =>
      simp only [choice, Except.map] at success
      cases success
      exact replaceCache_eq edge result.cached

/-- A successful raw-state replay returns the exact original prepared edge. -/
theorem replayRaw_eq_original (edge : PreparedEdge curve differential)
    (raw : PreparedRawStateReplay.Checked _ edge.owner.ambient
      (PreparedRawStateReplay.capture edge.owner.track.initial))
    (restored : PreparedEdge curve differential)
    (success : replayRaw edge.segment edge.within edge.left edge.owner edge.request
      edge.ordered edge.sheet raw = .ok restored) : restored = edge := by
  unfold replayRaw at success
  cases choice : PreparedRawSourceReplay.replay edge.segment edge.left edge.owner edge.request raw rfl with
  | error failed => simp only [choice, Except.map] at success; cases success
  | ok result =>
      simp only [choice, Except.map] at success
      cases success
      exact replaceCache_eq edge result.cached

end Purelib.Riemann.Transport.PreparedEdgeReplay
