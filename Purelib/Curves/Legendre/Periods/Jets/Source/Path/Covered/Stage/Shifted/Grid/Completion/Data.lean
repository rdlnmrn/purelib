module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Data.Cache

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

namespace CompletionData

/-- Exact quantified whole common-cache readback on its original node, alignment and source. -/
abbrev CommonReadback : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    retained.common = ShiftedGeometry.Request.queryCachesOfAligned
      (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
      (admitted := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      (widths := widths) (blocks := node.common.blocks) (chain := chain) (roots := roots)
      node.common.requested.request node.common.geometry_eq old aligned alignedEq

/-- The whole original query cache is its original retained-Alignment factory on this SAME stored target. -/
theorem common_eq : CommonReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact retained.property.1

/-- Exact quantified target-query readback on the same retained common cache. -/
abbrev QueriesReadback : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    retained.queries = node.targetQueries retained.common.queries

/-- The next-view query operation keeps the exact pure original whole-factory transport. -/
theorem queries_eq : QueriesReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact retained.property.2.1

/-- Exact quantified target-completion readback on the same retained common cache. -/
abbrev CompletionReadback : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    retained.completion = node.targetCompletion retained.common.completion

/-- The next-view completion keeps the exact pure original whole-factory transport. -/
theorem completion_eq : CompletionReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact retained.property.2.2.1

/-- Quantified heterogeneous identity of the whole retained target and common query operations. -/
abbrev QueriesTransport : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    HEq retained.queries retained.common.queries

/-- The complete target query operation is retained heterogeneously across the actual source-index displays. -/
theorem queries_heq : QueriesTransport := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact (heq_of_eq retained.queries_eq).trans (node.targetQueries_heq retained.common.queries)

/-- Quantified heterogeneous identity of the whole retained target and common completions. -/
abbrev CompletionTransport : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    HEq retained.completion retained.common.completion

/-- The whole target Completion is retained heterogeneously, including all actual acquired endpoint work. -/
theorem completion_heq : CompletionTransport := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact (heq_of_eq retained.completion_eq).trans (node.targetCompletion_heq retained.common.completion)

/-- Exact quantified completed-family readback on the same stored literal-target completion. -/
abbrev FamilyReadback : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    retained.family = node.next.requested.request.completedFamily retained.completion

/-- The family is the original constructor on the SAME whole stored literal-target completion. -/
theorem family_eq : FamilyReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact retained.property.2.2.2

/-- Exact quantified selected-family readback retaining the original target attempt and completion. -/
abbrev SelectedFamilyReadback : Prop :=
  ∀
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
    (retained : CompletionData node aligned alignedEq old),
    (retained.family node.next.requested.selected.stage).val =
    (⟨node.next.requested.request.attempt, retained.completion⟩ : Completed
      (parameter := parameter + Sampling.gridOffset intervals index.succ direction) (frame := node.target)
      node.next.requested.request.covered node.next.requested.request.chain
      node.next.requested.selected.stage targetFloor targetRootStage)

/-- The selected family member retains this whole SAME original target attempt and Completion cache. -/
theorem family_at : SelectedFamilyReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained
  exact (congrArg (fun family : node.next.requested.request.attempt.CompletedFamily =>
    (family node.next.requested.selected.stage).val) retained.family_eq).trans
      (node.next.requested.request.completedFamily_at retained.completion)

end CompletionData

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
