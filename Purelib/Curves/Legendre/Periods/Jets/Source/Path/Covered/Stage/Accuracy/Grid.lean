module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid

/-! # Actual common-accuracy source caches at positive absolute parameter nodes

A common local-fourth/spatial request is exactly its own minimum with the
absolute-fourth request at every positive grid node. The same actual source
Requested and its same completed family member are transported together.
The resulting original Requested is accepted by the existing shifted and
ValueBlocks factories; no source request or completion is executed again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Variation

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (index : Fin intervals)
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest)

/-- The original positive-node request/member result type, with its complete selected-stage ownership.

This is the existing dependent pair from atPositiveGridNode, named exactly
so a retained shifted consumer can store that whole original cache. It adds
no data fields and computes no source selection or completed family member.
-/
@[expose] def PositiveGridRequest :=
  let common := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
    (Sampling.gridIncrement_nonzero intervals positive direction moving))
  let absolute := Sampling.incrementRequest (Sampling.gridOffset intervals index.succ direction)
    (Sampling.gridOffset_nonzero intervals positive index direction moving)
  (paid : Requested covered chain current floor rootStage (common.minimum absolute)) ×
  { value : Completed covered chain paid.selected.stage floor rootStage // value.1 = paid.attempt }

variable (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })

/-- Retain the SAME common-accuracy source and completed member at one actual positive absolute-node request index.

The original grid index is a successor, so its nonzero absolute offset and
whole minimum equality are derived rather than assumed. Existing source,
selection, Targets, prepared models, bank/checks, Commons and completion
remain the same caches. Node zero is the original source itself and is not
passed through this moving absolute-node constructor.
-/
def atPositiveGridNode :
    PositiveGridRequest (covered := covered) (chain := chain) (current := current)
      (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial :=
  source.castAccuracyMember
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm member

/-- The original positive-node factory reads exactly the supplied source at its equal whole accuracy index.

The equality concerns the whole original Requested cache, including its
selected stage, original attempt and exact preparation/allocation owners.
It is a readback of the existing factory rather than another acquisition.
-/
theorem atPositiveGridNode_requested_eq :
    (atPositiveGridNode intervals positive index direction moving spatial source member).1 =
      source.castAccuracy (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm := by
  exact source.castAccuracyMember_source
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm member

/-- The positive-node request retains the SAME whole original source Requested value, without acquisition replay. -/
theorem atPositiveGridNode_requested_heq :
    HEq (atPositiveGridNode intervals positive index direction moving spatial source member).1 source := by
  exact (heq_of_eq (atPositiveGridNode_requested_eq intervals positive index direction moving spatial
    source member)).trans (source.castAccuracy_heq
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm)

/-- The positive-node request retains the SAME entire completed-member subtype and its original attempt identity. -/
theorem atPositiveGridNode_member_heq :
    HEq (atPositiveGridNode intervals positive index direction moving spatial source member).2 member := by
  exact source.castAccuracyMember_member_heq
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm member

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
