module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Table
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Completion
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Data.Prod.Factories
public import Purelib.Data.Vector.Dependent.Subtype

/-! # Completion of each literal retained positive-node target

The stored common Blocks, exact outgoing occurrences and shared Alignment
products propagate genuine old query agreement before the original target
attempt completes. Exact source-accuracy transport retains that whole
completion on node.next. Its own original completed family is constructed
once, with no target Completion, Ready or final sample relation as an input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

universe u

/-- Equality elimination retains the whole original value heterogeneously. -/
private theorem mp_heq {first last : Sort u} (equal : first = last) (value : first) :
    HEq (Eq.mp equal value) value := by
  cases equal
  rfl

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}

section Node

variable {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

/-- Transport the SAME target all-query operation from the stored common view to literal node.next. -/
def targetQueries
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (queries : QueryAgreement node.common.requested.prepared) :
    QueryAgreement node.next.requested.prepared :=
  ofSourceAccuracyQueries
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source node.paid.1
    node.source_eq node.next
    (Eq.mp (congrArg (fun retained : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := node.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage => QueryAgreement retained.requested.prepared)
        node.common_eq) queries)

/-- Pure whole-factory transport preserves the entire original target-query operation heterogeneously. -/
theorem targetQueries_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (queries : QueryAgreement node.common.requested.prepared) :
    HEq (node.targetQueries queries) queries := by
  unfold targetQueries
  exact (ofSourceAccuracyQueries_heq
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source node.paid.1
    node.source_eq node.next _).trans (mp_heq _ queries)

/-- Transport the SAME complete target acquisitions and Stage from the stored common view to literal node.next. -/
def targetCompletion
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (completed : Completion node.common.requested.request.attempt) :
    Completion node.next.requested.request.attempt :=
  ofSourceAccuracyCompletion
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source node.paid.1
    node.source_eq node.next
    (Eq.mp (congrArg (fun retained : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := node.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage => Completion retained.requested.request.attempt)
        node.common_eq) completed)

/-- Pure whole-factory transport retains every original target Completion cache without reacquisition. -/
theorem targetCompletion_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (completed : Completion node.common.requested.request.attempt) :
    HEq (node.targetCompletion completed) completed := by
  unfold targetCompletion
  exact (ofSourceAccuracyCompletion_heq
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source node.paid.1
    node.source_eq node.next _).trans (mp_heq _ completed)

end Node

section NodeData

variable {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)

/-- The EXACT existing Request.QueryCaches application on this SAME stored common-view target. -/
@[expose] def CommonCaches
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (old : QueryAgreement source.prepared)
    := ShiftedGeometry.Request.QueryCaches
  (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
  (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
  (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
  node.common.requested.request node.common.geometry_eq old

namespace CompletionData

/-- The original all-query operation type on this literal node.next preparation. -/
@[expose] def TargetQueries
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : Type _ := QueryAgreement node.next.requested.prepared

/-- The original complete-acquisition type on this literal node.next attempt. -/
@[expose] def TargetCompletion
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : Type _ := Completion node.next.requested.request.attempt

/-- The original completed-family type on this literal node.next attempt. -/
@[expose] def TargetFamily
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : Type _ := node.next.requested.request.attempt.CompletedFamily

/-- The SAME original common-cache value has its whole retained-Alignment factory equality. -/
@[expose] def CommonFactory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)
    (common : CommonCaches node old) : Prop :=
  common = ShiftedGeometry.Request.queryCachesOfAligned
    (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
    (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
    (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
    node.common.requested.request node.common.geometry_eq old aligned alignedEq

/-- The literal target query operation is the original whole transport of this SAME common-cache operation. -/
@[expose] def QueriesFactory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (old : QueryAgreement source.prepared) (common : CommonCaches node old)
    (queries : TargetQueries node) : Prop :=
  queries = node.targetQueries common.queries

/-- The literal target completion is the original whole transport of this SAME common-cache completion. -/
@[expose] def CompletionFactory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (old : QueryAgreement source.prepared) (common : CommonCaches node old)
    (completion : TargetCompletion node) : Prop :=
  completion = node.targetCompletion common.completion

/-- The original completed family is constructed from this SAME stored literal-target completion. -/
@[expose] def FamilyFactory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (completion : TargetCompletion node) (family : TargetFamily node) : Prop :=
  family = node.next.requested.request.completedFamily completion

end CompletionData

/-- Original QueryCaches, exact next-view query/completion transports and the original completed target family.

The four runtime carriers are fixed by the same node and old query owner.
Their ordinary product retains each original value once; its subtype keeps
all four whole factory equations on those exact values. Only whole
source-accuracy equality carries the common cache to literal node.next;
no occurrence, query, completion or bank algorithm is copied or replayed.
-/
@[expose] def CompletionData
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)
    : Type _ :=
  { values : CommonCaches node old × CompletionData.TargetQueries node ×
      CompletionData.TargetCompletion node × CompletionData.TargetFamily node //
    CompletionData.CommonFactory node aligned alignedEq old values.1 ∧
    CompletionData.QueriesFactory node old values.1 values.2.1 ∧
    CompletionData.CompletionFactory node old values.1 values.2.2.1 ∧
    CompletionData.FamilyFactory node values.2.2.1 values.2.2.2 }

namespace CompletionData

/-- The exact aliases retain all four original values and their whole factories in one certified product. -/
private theorem layout_eq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)
    : CompletionData node aligned alignedEq old =
  { values : CommonCaches node old × QueryAgreement node.next.requested.prepared ×
      Completion node.next.requested.request.attempt × node.next.requested.request.attempt.CompletedFamily //
    values.1 = ShiftedGeometry.Request.queryCachesOfAligned
      (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
      (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
      node.common.requested.request node.common.geometry_eq old aligned alignedEq ∧
    values.2.1 = node.targetQueries values.1.queries ∧
    values.2.2.1 = node.targetCompletion values.1.completion ∧
    values.2.2.2 = node.next.requested.request.completedFamily values.2.2.1 } := rfl

/-- Derive actual target query caches from the SAME stored Alignment, then retain their whole next-view completion. -/
def build
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)
    : CompletionData node aligned alignedEq old :=
  Data.Prod.ofSubtypeFactories
    (α := CommonCaches node old)
    (β := TargetQueries node)
    (γ := TargetCompletion node)
    (δ := TargetFamily node)
    (fun _ => ShiftedGeometry.Request.queryCachesOfAligned
      (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
      (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
      node.common.requested.request node.common.geometry_eq old aligned alignedEq)
    (fun common => node.targetQueries common.queries)
    (fun common _ => node.targetCompletion common.completion)
    (fun _ _ nextCompleted => node.next.requested.request.completedFamily nextCompleted)

/-- The builder retains the COMPLETE original four-let factory value and its original order. -/
private theorem build_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align))
    (old : QueryAgreement source.prepared)
    : build node aligned alignedEq old =
    (let common : CommonCaches node old := ShiftedGeometry.Request.queryCachesOfAligned
         (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
         (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
         (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
         node.common.requested.request node.common.geometry_eq old aligned alignedEq
     let nextQueries : QueryAgreement node.next.requested.prepared := node.targetQueries common.queries
     let nextCompleted : Completion node.next.requested.request.attempt := node.targetCompletion common.completion
     let family : node.next.requested.request.attempt.CompletedFamily :=
       node.next.requested.request.completedFamily nextCompleted
     ⟨⟨common, nextQueries, nextCompleted, family⟩, ⟨rfl, rfl, rfl, rfl⟩⟩) := rfl

variable {node aligned alignedEq old} (retained : CompletionData node aligned alignedEq old)

/-- Read the SAME original Request.QueryCaches, including both original occurrence and supplied Alignment products. -/
@[expose] def common
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    : CommonCaches node old := retained.val.1

/-- Read the SAME transported all-query operation on literal node.next's actual preparation. -/
@[expose] def queries
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    : QueryAgreement node.next.requested.prepared := retained.val.2.1

/-- Read the SAME complete acquisitions and Stage on literal node.next's original target attempt. -/
@[expose] def completion
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    : Completion node.next.requested.request.attempt := retained.val.2.2.1

/-- Read the original completed family closure retaining this SAME selected target Completion. -/
@[expose] def family
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    : node.next.requested.request.attempt.CompletedFamily := retained.val.2.2.2

end CompletionData

end NodeData

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
