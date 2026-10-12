module
import Purelib.Data.Vector.Basic

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Mesh.Replay.DualReplay

open Purelib

open Purelib.Data.List

open Purelib.Topology.Mesh.Replay

open Purelib.Topology.Mesh.Replay.DualReplay

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

open Purelib.Topology.Surface.Sewing.SewingForest
open _root_.Purelib.Topology.Surface.Sewing renaming SewingForest -> SewingForest

open Purelib.Topology.Surface.Sewing.SewingTree
open _root_.Purelib.Topology.Surface.Sewing renaming SewingTree -> SewingTree

@[expose] public section

/-!
Exact regressions for evidence-bearing sewing and dual-path invalidity.
The checks inspect failure variants and cached locations, not only acceptance
bits. Negative permutation and position proofs are consumed directly.
-/

namespace Test.Topology.Surface.Sewing.Diagnostics

open Purelib.Topology.Polygon.Stokes (OrientedTriangle)

/-- The two oriented triangles forming the sewing regression patch. -/
private def faces (index : Fin 2) : Stokes.OrientedTriangle 4 :=
  if index.val = 0 then ⟨0, 1, 2⟩ else ⟨0, 2, 3⟩

/-- Extract the retained invalidity evidence from a certified failed result. -/
private def rejected {Error Value : Type} (result : Except Error Value) (failed : result.isOk = false) : Error := by
  cases result with
  | error invalid => exact invalid
  | ok value => cases failed

/-- Test the evidence of a failed result, returning false for success. -/
private def rejectsWith {Error Value : Type} (result : Except Error Value) (test : Error → Bool) : Bool :=
  match result with
  | .error invalid => test invalid
  | .ok _ => false

/-- The rejected boundary position supplies its out-of-bounds inequality. -/
example : (faces 0).boundary.length ≤ 3 :=
  (rejected (BoundarySplit.checkAt (faces 0).boundary 3) (by decide)).outOfBounds

/-- The accepted boundary split retains the requested prefix length. -/
example : ((BoundarySplit.checkAt (faces 0).boundary 2).toOption.get (by decide)).split.before.length = 2 :=
  ((BoundarySplit.checkAt (faces 0).boundary 2).toOption.get (by decide)).position_eq

/-- Duplicate entries produce direct evidence that the lists are not permutations. -/
example : ¬ List.Perm ([0, 0] : List Nat) [0, 1] :=
  (rejected (Permutation.certify ([0, 0] : List Nat) [0, 1]) (by decide)).notPerm

/-- Different list lengths produce direct non-permutation evidence. -/
example : ¬ List.Perm ([0] : List Nat) [0, 1] :=
  (rejected (Permutation.certify ([0] : List Nat) [0, 1]) (by decide)).notPerm

/-- Permutation rejection retains the unmatched final entry. -/
example : rejectsWith (Permutation.certify ([0, 0] : List Nat) [0, 1])
    (fun invalid => match invalid with
      | .matched _ _ _ remaining _ (.missing _ _ _ _) => remaining == [1]
      | _ => false) = true := by decide

/-- The first triangle as an unsown certified patch. -/
private def first := SewnPatch.triangle faces 0
/-- The second triangle as an unsown certified patch. -/
private def second := SewnPatch.triangle faces 1

/-- Sewing rejects an out-of-bounds position in the first patch. -/
example : rejectsWith (SewingTree.SewnPatch.checkSew first second 3 0)
    (fun invalid => match invalid with | .firstPosition _ => true | _ => false) = true := by decide

/-- A second-position rejection retains the valid first split. -/
example : rejectsWith (SewingTree.SewnPatch.checkSew first second 2 3)
    (fun invalid => match invalid with
      | .secondPosition cached _ => cached.split.before.length == 2
      | _ => false) = true := by decide

/-- Orientation rejection retains both selected edge endpoints. -/
example : rejectsWith (SewingTree.SewnPatch.checkSew first second 0 0)
    (fun invalid => match invalid with
      | .orientation cachedFirst cachedSecond _ =>
          cachedFirst.split.edge.start.val == 0 && cachedSecond.split.edge.finish.val == 2
      | _ => false) = true := by decide

/-- The two-leaf sewing tree with incompatible selected edge orientations. -/
private def badTree : Topology.Surface.Sewing.SewingTree 2 := .join (.leaf 0) (.leaf 1) 0 0
/-- The two-leaf sewing tree joining the oppositely oriented common edge. -/
private def goodTree : Topology.Surface.Sewing.SewingTree 2 := .join (.leaf 0) (.leaf 1) 2 0

/-- Successful replay preserves the exact original sewing tree. -/
example : ((SewingTree.SewnPatch.replay faces goodTree).toOption.get (by decide)).patch.tree =
  goodTree :=
  ((SewingTree.SewnPatch.replay faces goodTree).toOption.get (by decide)).tree_eq

/-- A failed left subtree is reported at node path [0]. -/
example : (rejected (SewingTree.SewnPatch.replay faces (.join badTree (.leaf 0) 0
  0)) (by decide)).nodePath = [0] := by decide
/-- A failed right subtree is reported at node path [1]. -/
example : (rejected (SewingTree.SewnPatch.replay faces (.join (.leaf 0) badTree 0
  0)) (by decide)).nodePath = [1] := by decide

/-- Forest replay failure retains its successful prefix and failed node path. -/
example : rejectsWith (SewingForest.checkTrees faces [.leaf 0, badTree])
    (fun invalid => match invalid with
      | .replay report => report.before.length == 1 && report.after.isEmpty && report.invalid.nodePath.isEmpty
      | _ => false) = true := by decide

/-- Incomplete face coverage retains the single checked patch. -/
example : rejectsWith (SewingForest.checkTrees faces [.leaf 0])
    (fun invalid => match invalid with | .coverage checked _ => checked.patches.length == 1 | _ => false) = true := by
      decide

/-- Duplicated face coverage retains all three checked patches. -/
example : rejectsWith (SewingForest.checkTrees faces [.leaf 0, .leaf 1, .leaf 0])
    (fun invalid => match invalid with | .coverage checked _ => checked.patches.length == 3 | _ => false) = true := by
      decide

/-- A nonmaximal forest retains its two separate checked patches. -/
example : rejectsWith (SewingForest.checkTrees faces [.leaf 0, .leaf 1])
    (fun invalid => match invalid with | .nonmaximal checked _ => checked.patches.length == 2 | _ => false) = true := by
      decide

/-- Dual replay rejects an invalid first edge position. -/
example : rejectsWith (DualWalk.replay faces 0 1 [⟨1, 3, 0⟩])
    (fun invalid => match invalid with | .firstPosition .. => true | _ => false) = true := by decide

/-- Dual replay rejects an invalid next position while retaining the first split. -/
example : rejectsWith (DualWalk.replay faces 0 1 [⟨1, 2, 3⟩])
    (fun invalid => match invalid with
      | .nextPosition _ _ cached _ => cached.split.before.length == 2
      | _ => false) = true := by decide

/-- Dual replay rejects inconsistent edge orientation. -/
example : rejectsWith (DualWalk.replay faces 0 1 [⟨1, 0, 0⟩])
    (fun invalid => match invalid with | .orientation .. => true | _ => false) = true := by decide

/-- A terminal endpoint mismatch is reported at offset one. -/
example : (rejected (DualWalk.replay faces 0 0 [⟨1, 2, 0⟩]) (by decide)).offset = 1 := by decide

/-- The terminal endpoint mismatch retains the preceding successful dual step. -/
example : rejectsWith (DualWalk.replay faces 0 0 [⟨1, 2, 0⟩])
    (fun invalid => match invalid with | .tail _ _ _ _ _ (.endpoint _) => true | _ => false) = true := by decide

/-- Empty dual paths to both faces, including the unreachable second face. -/
private def badPaths : Data.Vector (List (DualReplay.DualStep 2)) 2 :=
  .cons [] (.cons [] .nil)

/-- The failed dual connection identifies the second face. -/
example : (rejected (DualConnection.checkPaths faces 0 badPaths) (by
  decide)).index.val = 1 := by decide
/-- The failed dual connection retains the checked first face as its exact prefix. -/
example : ((rejected (DualConnection.checkPaths faces 0 badPaths) (by
  decide)).checkedPrefix.map
    (fun checked => checked.1.val)) = [0] := by decide

end Test.Topology.Surface.Sewing.Diagnostics
