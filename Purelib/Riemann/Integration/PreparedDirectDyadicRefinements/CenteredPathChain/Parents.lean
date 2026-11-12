module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Centered chains assembled from their retained parent records

The supplied parent list is the computational spine. Existence of its
original centered chain supplies only endpoint identities and existence of
the literal remaining chain, all in Prop. No original preparation is read
again, and no computational chain is selected from Nonempty.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Read an actual direct parent chain as the same ordered centered chain.

Both original indexed chain types retain the same actual parent and exact
lifted endpoint roles. Structural conversion preserves stationary and
repeated occurrences and computes no edge, sheet or root owner.
-/
def ofDirect : {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    DirectPathChain parents (start := start) (finish := finish) →
      CenteredPathChain parents (start := start) (finish := finish)
  | _, _, _, .nil point => .nil point
  | _, _, _, .cons parent remaining => .cons parent (ofDirect remaining)

/-- The original centered path has exactly one lifted cell per literal parent occurrence.

Stationary or repeated physical edges remain distinct entries. Only a
nil chain has no cell; no sheet or root-owner identification is involved.
-/
theorem path_cellCount :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
      chain.path.cellCount = parents.length
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons _ tail => congrArg Nat.succ (path_cellCount tail)

/-- Construct the centered chain directly from the supplied ordered parent records.

Only the list supplies computational data. The original chain's existence
is eliminated into propositions proving the exact source, target and
remaining-chain indices; every parent and its original sheet are retained.
-/
def ofParents :
    (parents : List (CenteredEdge curve differential)) → {start finish : LiftedPoint 2} →
      Nonempty (CenteredPathChain parents (start := start) (finish := finish)) →
        CenteredPathChain parents (start := start) (finish := finish)
  | [], start, finish, hasChain =>
      have endpoints : start = finish := by
        obtain ⟨chain⟩ := hasChain
        exact chain.empty_eq
      (CenteredPathChain.nil start).castFinish endpoints
  | parent :: parents, start, finish, hasChain =>
      have first :
          (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2) =
            start := by
        obtain ⟨chain⟩ := hasChain
        exact chain.start_eq
      have remaining : Nonempty (CenteredPathChain parents
          (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)
          (finish := finish)) := by
        obtain ⟨chain⟩ := hasChain
        exact ⟨chain.remaining⟩
      (CenteredPathChain.cons parent (ofParents parents remaining)).castStart first

/-- Direct assembly retains the entire original centered chain, not merely its coordinates. -/
theorem ofParents_eq {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    ofParents parents ⟨chain⟩ = chain := by
  induction chain with
  | nil point => rfl
  | cons parent tail ih =>
      change CenteredPathChain.cons parent (ofParents _ _) = CenteredPathChain.cons parent tail
      exact congrArg (fun remaining => CenteredPathChain.cons parent remaining) ih

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

end
