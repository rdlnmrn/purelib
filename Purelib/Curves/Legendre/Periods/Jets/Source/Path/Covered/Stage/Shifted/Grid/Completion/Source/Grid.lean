module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Following
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source.Table
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Table
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Trace
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment

/-! # The five retained grid factories on one actual requested source

The same original node and incoming CompletionData supply one sufficient
source pair and its transported query operation. The original target table,
its completions and sample trace keep those same cached inputs and all
five whole factory predicates in their existing Sigma/Subtype layout.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)
namespace PositiveGridNode.CompletionData.RequestedSource

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

/-- The same five original cached values and whole factory equations at one retained target node.

The sufficient source pair is selected from the incoming CompletionData.
All later fields depend on that same pair, its original query operation
and the one original nominal table; no later source or target completion
is a premise.
-/
@[expose] def Grid
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) : Type _ :=
  let nextFrame := node.target
  let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  node.next.requested.asSource.FollowingGrid
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots nextTargetCurrent nextTargetFloor nextTargetRootStage
    (fun _ => incoming.requestedSource nextCurrent nextAccuracy)
    (fun (common : RequestedSource node nextCurrent nextAccuracy) =>
      RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming)

namespace Grid

/-- The complete dependent-fibre identity for every original requested grid and its two factories.

All original source, geometry, query, table and completion indices remain
inside this exact proposition. Its closed form keeps theorem metadata from
reclassifying the dependent cached-data arguments.
-/
@[expose] def RequestFibreEquation : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat),
    Grid
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage =
      (let nextFrame := node.target
       let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
       let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
       let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
         (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
           (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
       let nextRoots := PreparedBankRootChains.RootChain.castChildren
         node.next.requested.request.shape.property node.next.geometry.roots
       (common : { value : RequestedSource node nextCurrent nextAccuracy //
         value = incoming.requestedSource nextCurrent nextAccuracy }) ×
       (queries : { value : RequestedSource.Queries node nextCount positiveCount nextDirection nextMoving
         nextSpatial nextCurrent common.val //
         value = RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
           nextSpatial nextCurrent common.val incoming }) ×
       (table : { value : RequestedSource.Table node nextCount positiveCount nextDirection nextMoving
         nextSpatial nextCurrent common.val nextRanges nextAllocation nextAdmitted nextWidths
         nextTargetCurrent nextTargetFloor nextTargetRootStage //
         value = PositiveGridNode.Table.build (frame := nextFrame) (basis := basis) (count := count)
         (parent := node.next.requested.request.shape.val.1)
         (parents := node.next.requested.request.shape.val.2)
         (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
         (current := max nextCurrent (node.next.requested.selected.stage + 1))
         (floor := targetFloor) (rootStage := targetRootStage)
           nextCount positiveCount nextDirection nextMoving
           (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial)
           common.val.1 common.val.2 nextRanges nextAllocation nextAdmitted nextWidths nextRoots
           nextTargetCurrent nextTargetFloor nextTargetRootStage }) ×
       (_completions : { value : RequestedSource.Table.Completions table.val queries.val //
         value = PositiveGridNode.Table.Completions.build table.val queries.val }) ×
       { value : RequestedSource.Table.Trace table.val // value = PositiveGridNode.Table.Trace.build table.val })

/-- The complete original node Grid is exactly the raw endpoint-Request fibre with its SAME two actual factories.

Every source/member, query, table, completion and trace field retains its
original pointwise factory predicate. This is definitional specialization;
no operation is invoked and no cache or nominal parent is replaced.
-/
theorem requestFibre_eq : RequestFibreEquation := by
  unfold RequestFibreEquation
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old incoming nextDirection nextMoving nextSpatial
    nextCurrent nextRefinement nextPositive nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent
    nextTargetFloor nextTargetRootStage
  rfl

/-- Package this SAME already-built node Grid with its literal endpoint Request and all original geometry inputs.

Only the original ranges, allocation, admission, widths and two operation
values are retained around the same five caches. No source selection,
reprepare callback, table, completion or sample trace factory is invoked.
-/
@[expose] def window
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (cached : Grid
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage) :
    StageAttempt.Requested.FollowingGrid.Window
      (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
      (frame := node.target) (basis := basis) (count := count)
      (parent := node.next.requested.request.shape.val.1)
      (parents := node.next.requested.request.shape.val.2)
      (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
      (endpoint := node.next.requested.asSource)
      (roots := PreparedBankRootChains.RootChain.castChildren
        node.next.requested.request.shape.property node.next.geometry.roots)
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextTargetCurrent nextTargetFloor nextTargetRootStage :=
  let nextFrame := node.target
  let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  StageAttempt.Requested.FollowingGrid.ofGrid
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    node.next.requested.asSource nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots
    nextTargetCurrent nextTargetFloor nextTargetRootStage
    (fun _ => incoming.requestedSource nextCurrent nextAccuracy)
    (fun (common : RequestedSource node nextCurrent nextAccuracy) =>
      RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming) cached

/-- The exact retained-cache equation for every original requested endpoint window.

All original source, geometry, query, table and completion indices remain
inside this exact proposition. Its closed form keeps theorem metadata from
reclassifying the dependent cached-data arguments.
-/
@[expose] def WindowCacheEquation : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (cached : Grid
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage),
    (window
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
      cached).cache = cached

/-- The raw endpoint window reads the complete SAME original five-cache node Grid, including every factory predicate. -/
theorem window_cache : WindowCacheEquation := by
  unfold WindowCacheEquation
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old incoming nextDirection nextMoving nextSpatial
    nextCurrent nextRefinement nextPositive nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent
    nextTargetFloor nextTargetRootStage cached
  let nextFrame := node.target
  let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  exact StageAttempt.Requested.FollowingGrid.cache_ofGrid
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    node.next.requested.asSource nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots
    nextTargetCurrent nextTargetFloor nextTargetRootStage
    (fun _ => incoming.requestedSource nextCurrent nextAccuracy)
    (fun (common : RequestedSource node nextCurrent nextAccuracy) =>
      RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming) cached

/-- Execute the five original grid factories once in source/query/table/completion/trace order.

The original endpoint-grid builder retains each entire value and its
exact equation. It consumes the same source and query operations without
expanding the node's dependent table tail or replaying any factory.
-/
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) :
    Grid
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage := by
  dsimp only [Grid]
  let nextFrame := node.target
  let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  exact StageAttempt.Requested.FollowingGrid.build
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    node.next.requested.asSource nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots
    nextTargetCurrent nextTargetFloor nextTargetRootStage
    (fun _ => incoming.requestedSource nextCurrent nextAccuracy)
    (fun (common : RequestedSource node nextCurrent nextAccuracy) =>
      RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming)

/-- The complete per-window equality with the original five-let execution and its unchanged tuple.

This exact proposition names the full factory readback without changing
the retained data or introducing a new execution. It is pointwise in the
actual admitted range/strip/width inputs, rather than function equality.
-/
@[expose] def Factory
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (value :
      Grid
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage)
        (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
        (spatial := spatial) (source := source) (member := member)
        (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
        (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (index := index)
        (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
        nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
        nextRanges nextAllocation nextAdmitted nextWidths
        nextTargetCurrent nextTargetFloor nextTargetRootStage) : Prop :=
  value =
    let nextFrame := node.target
    let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
    let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
    let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
      (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
        (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
    let nextRoots := PreparedBankRootChains.RootChain.castChildren
      node.next.requested.request.shape.property node.next.geometry.roots
    let common := incoming.requestedSource nextCurrent nextAccuracy
    let queries := RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming
    let table := PositiveGridNode.Table.build (frame := nextFrame) (basis := basis) (count := count)
      (parent := node.next.requested.request.shape.val.1)
      (parents := node.next.requested.request.shape.val.2)
      (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
      (current := max nextCurrent (node.next.requested.selected.stage + 1))
      (floor := targetFloor) (rootStage := targetRootStage)
      nextCount positiveCount nextDirection nextMoving
      (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial)
      common.1 common.2 nextRanges nextAllocation nextAdmitted nextWidths nextRoots
      nextTargetCurrent nextTargetFloor nextTargetRootStage
    let completions := PositiveGridNode.Table.Completions.build table queries
    let trace := PositiveGridNode.Table.Trace.build table
    ⟨⟨common, rfl⟩, ⟨queries, rfl⟩, ⟨table, rfl⟩, ⟨completions, rfl⟩, ⟨trace, rfl⟩⟩

/-- The original node builder specializes the endpoint owner's complete five-factory law. -/
private theorem built_factory
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) :
    Factory
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
      (build
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage)
        (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
        (spatial := spatial) (source := source) (member := member)
        (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
        (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (index := index)
        (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
        nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
        nextRanges nextAllocation nextAdmitted nextWidths
        nextTargetCurrent nextTargetFloor nextTargetRootStage) := by
  let nextFrame := node.target
  let nextCount := PositiveGridNode.coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := PositiveGridNode.fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (PositiveGridNode.connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  exact StageAttempt.Requested.FollowingGrid.build_factory
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    node.next.requested.asSource nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots
    nextTargetCurrent nextTargetFloor nextTargetRootStage
    (fun _ => incoming.requestedSource nextCurrent nextAccuracy)
    (fun (common : RequestedSource node nextCurrent nextAccuracy) =>
      RequestedSource.reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent common incoming)

/-- The complete five-factory equation for every original retained grid execution.

All original source, geometry, query, table and completion indices remain
inside this exact proposition. Its closed form keeps theorem metadata from
reclassifying the dependent cached-data arguments.
-/
@[expose] def BuildEquation : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
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
    {targetCurrent targetFloor targetRootStage : Nat} {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (incoming : CompletionData node aligned alignedEq old)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (nextRanges : Range node)
    (nextAllocation : Range.Allocation node nextRanges)
    (nextAdmitted : Range.Admission node nextRanges nextAllocation nextDirection)
    (nextWidths : Widths node)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat),
    Factory
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
      nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
      (build
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage)
        (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
        (spatial := spatial) (source := source) (member := member)
        (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
        (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (index := index)
        (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
        nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
        nextRanges nextAllocation nextAdmitted nextWidths
        nextTargetCurrent nextTargetFloor nextTargetRootStage)

/-- The original builder retains the full same ordered five-let execution, including every factory predicate. -/
theorem build_eq : BuildEquation := by
  unfold BuildEquation
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old incoming nextDirection nextMoving nextSpatial
    nextCurrent nextRefinement nextPositive nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent
    nextTargetFloor nextTargetRootStage
  exact built_factory
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage)
    (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
    (spatial := spatial) (source := source) (member := member)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (index := index)
    (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old) incoming
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage

end Grid

end PositiveGridNode.CompletionData.RequestedSource
end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
