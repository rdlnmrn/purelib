module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Vector.Basic
public import Purelib.Data.Fin

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Mesh.DualWalks
public import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

@[expose] public section

/-!
# Exact replay of untrusted finite dual-connection paths

Generators supply face indices and the two edge positions for every step.
The checker neither repairs a failed position nor searches for a new route.
The checked walks are cached before constructing the root-to-face accessor.
-/

namespace Purelib.Topology.Mesh.Replay.DualReplay

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

open Purelib.Topology.Mesh.DualWalks

open Purelib.Topology.Polygon.Stokes (OrientedTriangle)

set_option genInjectivity false in
/-- One supplied step of a finite dual-face route.

It identifies the next face and the boundary positions to be checked on the current and next faces. -/
structure DualStep (faceCount : Nat) where
  /-- Target face of this supplied route step. -/ next : Fin faceCount
  /-- Requested edge position in the current face boundary. -/ firstPosition : Nat
  /-- Requested opposite edge position in the next face boundary. -/ nextPosition : Nat

constructive_injectivity DualStep

namespace DualWalk

variable {vertexCount faceCount : Nat}

set_option genInjectivity false in
open Purelib.Topology.Mesh.Replay in
/-- A precise failure of the supplied finite path. A tail failure retains the valid preceding step, so its location is
certified without a replay. -/
inductive InvalidReplay (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) :
    (first last : Fin faceCount) → List (DualReplay.DualStep faceCount) → Type where
  /-- The supplied route ends before reaching its required final face. -/ | endpoint {first last} (different : first ≠
    last) : Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces first last []
  /-- The requested position is invalid in the current face boundary. -/ | firstPosition {first last} (step :
    DualReplay.DualStep faceCount) (remaining : List (DualReplay.DualStep faceCount))
      (invalid : BoundarySplit.InvalidPosition (faces first).boundary step.firstPosition) :
      Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces first last (step :: remaining)
  /-- The next-face position is invalid after retaining the valid current position. -/ | nextPosition {first last} (step
    : DualReplay.DualStep faceCount) (remaining : List (DualReplay.DualStep faceCount))
      (firstAt : BoundarySplit.Positioned (faces first).boundary step.firstPosition)
      (invalid : BoundarySplit.InvalidPosition (faces step.next).boundary step.nextPosition) :
      Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces first last (step :: remaining)
  /-- Both positions exist but the displayed edges have incompatible orientations. -/ | orientation {first last} (step :
    DualReplay.DualStep faceCount) (remaining : List (DualReplay.DualStep faceCount))
      (firstAt : BoundarySplit.Positioned (faces first).boundary step.firstPosition)
      (nextAt : BoundarySplit.Positioned (faces step.next).boundary step.nextPosition)
      (notOpposite : nextAt.split.edge ≠ firstAt.split.edge.reverse) :
      Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces first last (step :: remaining)
  /-- Retain a valid crossing followed by the exact failure of the remaining route. -/ | tail {first last} (step :
    DualReplay.DualStep faceCount) (remaining : List (DualReplay.DualStep faceCount))
      (firstAt : BoundarySplit.Positioned (faces first).boundary step.firstPosition)
      (nextAt : BoundarySplit.Positioned (faces step.next).boundary step.nextPosition)
      (opposite : nextAt.split.edge = firstAt.split.edge.reverse)
      (invalid : Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces step.next last remaining) :
        Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.InvalidReplay faces first last (step :: remaining)

constructive_injectivity InvalidReplay

open Purelib.Topology.Mesh.Replay.DualReplay in
/-- Count the valid preceding steps before the recorded replay failure. -/
def InvalidReplay.offset {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount} {first last raw} :
    DualWalk.InvalidReplay faces first last raw → Nat
  | .tail _ _ _ _ _ invalid => invalid.offset + 1
  | .endpoint .. | .firstPosition .. | .nextPosition .. | .orientation .. => 0

open Purelib.Topology.Mesh.Replay in
open Purelib.Topology.Mesh.Replay.DualReplay in
/-- This complete finite check certifies success or invalidity of the exact path supplied. Failure is not evidence that
no other connecting path exists. -/
def replay (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (first last : Fin faceCount) :
    (raw : List (DualReplay.DualStep faceCount)) → Except (DualWalk.InvalidReplay faces first last raw)
      (DualWalks.DualWalk faces first last)
  | [] => if same : first = last then .ok (same ▸ DualWalk.nil first) else .error (.endpoint same)
  | step :: remaining =>
      match BoundarySplit.checkAt (faces first).boundary step.firstPosition with
      | .error invalid => .error (.firstPosition step remaining invalid)
      | .ok firstAt =>
          match BoundarySplit.checkAt (faces step.next).boundary step.nextPosition with
          | .error invalid => .error (.nextPosition step remaining firstAt invalid)
          | .ok nextAt =>
              if opposite : nextAt.split.edge = firstAt.split.edge.reverse then
                match Purelib.Topology.Mesh.Replay.DualReplay.DualWalk.replay faces step.next last remaining with
                | .error invalid => .error (.tail step remaining firstAt nextAt opposite invalid)
                | .ok tail => .ok (.cons firstAt.split.edge firstAt.split.edge_mem
                    (by rw [← opposite]; exact nextAt.split.edge_mem) tail)
              else .error (.orientation step remaining firstAt nextAt opposite)

end DualWalk

namespace DualConnection

variable {vertexCount faceCount : Nat}

set_option genInjectivity false in
open Purelib.Topology.Mesh.Replay in
open Purelib.Topology.Mesh.Replay.DualReplay in
/-- The failing target and its exact raw path are tied together by the dependent type. Earlier successful walks are
retained, not recomputed. -/
structure InvalidBank (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (root : Fin faceCount)
    {size : Nat} (targets : Fin size → Fin faceCount) (raw : Fin size → List (DualReplay.DualStep faceCount)) where
  /-- Index of the target whose supplied route fails replay. -/ index : Fin size
  /-- Certified failure of that target's exact supplied route. -/ invalid : DualWalk.InvalidReplay faces root (targets
    index) (raw index)
  /-- Previously checked target indices with their retained successful dual walks. -/ checkedPrefix : List ((index : Fin
    size) × DualWalks.DualWalk faces root (targets index))

constructive_injectivity InvalidBank

open Purelib.Topology.Mesh.Replay.DualReplay.DualConnection
open Purelib.Topology.Mesh.Replay
open Purelib.Topology.Mesh.Replay.DualReplay
/-- Check each supplied root-to-target route and retain its exact dual walk.

A failure identifies its target index and preserves the successful prefix, so accepted paths are not replayed on access.
-/
def replayBank (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (root : Fin faceCount) :
    {size : Nat} → (targets : Fin size → Fin faceCount) → (raw : Fin size → List (DualReplay.DualStep faceCount)) →
    Except (DualConnection.InvalidBank faces root targets raw) ((index : Fin size) → DualWalks.DualWalk faces root
      (targets index))
  | 0, _, _ => .ok (fun index => Fin.elim0 index)
  | _ + 1, targets, raw =>
      match DualWalk.replay faces root (targets 0) (raw 0) with
      | .error invalid => .error ⟨0, invalid, []⟩
      | .ok first =>
          match replayBank faces root (fun index => targets index.succ) (fun index => raw index.succ) with
          | .error invalid => .error
              ⟨invalid.index.succ, invalid.invalid,
                ⟨0, first⟩ :: invalid.checkedPrefix.map (fun ⟨index, walk⟩ => ⟨index.succ, walk⟩)⟩
          | .ok tail => .ok (Data.Fin.casesByRecursion first tail)

/-- Every finite target is checked, including its exact final index. The result retains the checked walks rather than
rerunning the verifier on access. -/
def checkPaths (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (root : Fin faceCount)
    (paths : Data.Vector (List (DualReplay.DualStep faceCount)) faceCount) :
    Except (DualConnection.InvalidBank faces root (fun index => index) paths) (DualWalks.DualConnection faces) := do
  let checked ← replayBank faces root (fun index => index) paths
  pure ⟨root, checked⟩

end DualConnection

end Purelib.Topology.Mesh.Replay.DualReplay
