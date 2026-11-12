module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
public import Purelib.Riemann.Integration.PreparedEdgeRecasting

/-! # Original centered-chain source, tail and exact list transports

These projections retain the whole actual geometric spine. They expose
only its original constructor source and unchanged tail; exact parent-list
transport changes no curve, sheet, edge or endpoint cache.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- The actual first centered parent's physical source and sheet equal the original chain's starting point. -/
theorem start_eq {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain (parent :: parents) (start := start) (finish := finish)) :
    (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2) = start := by
  cases chain
  rfl

/-- Read the exact original geometric tail, retaining its whole original ending-point index. -/
@[expose] def remaining {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain (parent :: parents) (start := start) (finish := finish)) :
    CenteredPathChain parents
      (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)
      (finish := finish) :=
  match chain with
  | .cons _ tail => tail

/-- An original empty centered chain retains identical starting and finishing lifted points. -/
theorem empty_eq {start finish : LiftedPoint 2}
    (chain : CenteredPathChain (curve := curve) (differential := differential) []
      (start := start) (finish := finish)) : start = finish := by
  cases chain
  rfl

/-- The last original parent's retained requested endpoint is the original whole chain's finishing point. -/
theorem last_eq {parent : CenteredEdge curve differential} :
    (before : List (CenteredEdge curve differential)) → {start finish : LiftedPoint 2} →
    CenteredPathChain (before ++ [parent]) (start := start) (finish := finish) →
      (⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩ : LiftedPoint 2) =
        finish
  | [], _, _, chain => chain.remaining.empty_eq
  | _ :: before, _, _, chain => last_eq before chain.remaining
termination_by structural before => before

/-- Reindex an actual nonempty closed chain at its own original first parent's same physical point and sheet. -/
@[expose] def basedAtFirst {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)} {point : LiftedPoint 2}
    (chain : CenteredPathChain (parent :: parents) (start := point) (finish := point)) :
    CenteredPathChain (parent :: parents)
      (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
      (finish := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩) :=
  (chain.castStart chain.start_eq.symm).castFinish chain.start_eq.symm

/-- Transport the complete unchanged original centered chain along an exact equality of its parent list. -/
@[expose] def castParents {first second : List (CenteredEdge curve differential)}
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain first (start := start) (finish := finish)) (equal : first = second) :
    CenteredPathChain second (start := start) (finish := finish) := by
  cases equal
  exact chain

/-- A fixed original centered-parent list determines its complete endpoint chain uniquely. -/
theorem eq {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (first second : CenteredPathChain parents (start := start) (finish := finish)) : first = second := by
  induction first with
  | nil point => cases second; rfl
  | cons parent tail ih =>
      cases second with
      | cons _ otherTail =>
          have same := ih otherTail
          cases same
          rfl

/-- Construct the original centered chain by traversing its retained parent list.

The erased existence witness supplies only endpoint equalities and tail
existence. The data recursion consumes the actual list, forwarding each
complete parent literally without preparing a source or endpoint again.
-/
def ofNonempty : (parents : List (CenteredEdge curve differential)) →
    ∀ {start finish : LiftedPoint 2},
      Nonempty (CenteredPathChain parents (start := start) (finish := finish)) →
        CenteredPathChain parents (start := start) (finish := finish)
  | [], start, finish, given => by
      have equal : start = finish := by
        cases given with
        | intro chain => exact chain.empty_eq
      exact (CenteredPathChain.nil start).castFinish equal
  | parent :: parents, start, finish, given => by
      have aligned :
          (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2) = start ∧
            Nonempty (CenteredPathChain parents
              (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)
              (finish := finish)) := by
        cases given with
        | intro chain => exact ⟨chain.start_eq, ⟨chain.remaining⟩⟩
      exact (CenteredPathChain.cons parent (ofNonempty parents aligned.2)).castStart aligned.1

/-- The list-driven construction agrees with any original chain on the same retained parents and endpoints. -/
theorem ofNonempty_eq {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (given : Nonempty (CenteredPathChain parents (start := start) (finish := finish)))
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    ofNonempty parents given = chain := eq _ _

/-- The same retained recast parent list and its whole centered chain, with the exact original list-factory law. -/
@[expose] def Recast (target : Differential genus) (parents : List (CenteredEdge curve differential))
    (start finish : LiftedPoint 2) : Type _ :=
  (kept : { values : List (CenteredEdge curve target) //
    values = parents.map (PreparedEdgeRecasting.recastCenteredEdge target) }) ×
  CenteredPathChain kept.val (start := start) (finish := finish)

/-- Recast each original head ONCE and share that actual head between the retained list and centered chain.

The original prepared-edge fields are reused by the existing recaster. Its
new canonical coefficient center is legitimate new work and is not repeated
by a later list map or stage callback.
-/
def recast (target : Differential genus) :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    CenteredPathChain parents (start := start) (finish := finish) → Recast target parents start finish
  | [], _, _, .nil point => ⟨⟨[], rfl⟩, .nil point⟩
  | _ :: _, _, _, .cons parent tail =>
      let head := PreparedEdgeRecasting.recastCenteredEdge target parent
      let remaining := recast target tail
      let kept := head :: remaining.1.val
      ⟨⟨kept, congrArg (List.cons head) remaining.1.property⟩, .cons head remaining.2⟩

/-- Recasting an empty original centered cycle retains its same empty parent and chain caches. -/
theorem recast_nil (target : Differential genus) (point : LiftedPoint 2) :
    recast target (CenteredPathChain.nil (curve := curve) (differential := differential) point) =
      ⟨⟨[], rfl⟩, .nil point⟩ := (rfl)

/-- The complete nonempty recast factory shares its one recast head and same original retained tail. -/
theorem recast_cons (target : Differential genus) (parent : CenteredEdge curve differential)
    {parents : List (CenteredEdge curve differential)} {finish : LiftedPoint 2}
    (tail : CenteredPathChain parents
      (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)
      (finish := finish)) :
    recast target (.cons parent tail) =
      let head := PreparedEdgeRecasting.recastCenteredEdge target parent
      let remaining := recast target tail
      let kept := head :: remaining.1.val
      ⟨⟨kept, congrArg (List.cons head) remaining.1.property⟩, .cons head remaining.2⟩ := (rfl)

/-- The retained recast chain follows the SAME original lifted path and ordered occurrences. -/
theorem path_recast (target : Differential genus) :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (chain.recast target).2.path = chain.path
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons parent tail => by
      change Geometry.Path.Gaussian.Lifted.Basic.LiftedPath.cons
          (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
            parent.edge.sheet parent.edge.localSegment) (recast target tail).2.path =
        Geometry.Path.Gaussian.Lifted.Basic.LiftedPath.cons
          (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
            parent.edge.sheet parent.edge.localSegment) tail.path
      rewrite [path_recast target tail]
      rfl

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

end
