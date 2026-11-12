module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Models
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid.Adjacent
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Actual consecutive positive-node programmes on the SAME stored global Taylor rows

Whole original request equality provides only a new index display of each
retained target Request. Both actual common/next shifted caches stay owned.
The stored between-global rows then read the literal original targetProgram
samples at each programme's own retained selected stage, without another
shifted, source, target, model, programme, query or integral construction.
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
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry
  (ValueBlocks BetweenRows Position)
open Purelib.Data.Rat.Fraction (Rational)

section First

/-- Read the SAME whole first target Request at the exactly equal actual local-difference accuracy index. -/
@[expose] def firstRequested
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    : firstNode.common.requested.AtAccuracy
    (spatial.minimum (Sampling.incrementRequest (Sampling.gridPositiveIncrement intervals index following direction)
        (Sampling.gridPositiveDifference_nonzero intervals positive index following direction moving))) :=
  ShiftedGeometry.Requested.castAccuracy
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
    firstNode.common.requested

/-- The whole original first target Requested cache is retained by this exact accuracy view. -/
theorem firstRequested_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    : HEq (firstRequested (following := following) firstNode) firstNode.common.requested :=
  firstNode.common.requested.castAccuracy_heq
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm

/-- The actual selected first target stage is unchanged and remains its literal original programme stage. -/
theorem firstRequested_stage
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    :
    (firstRequested (following := following) firstNode).selected.stage = firstNode.next.requested.selected.stage :=
  (firstNode.common.requested.castAccuracy_stage
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm).trans
      firstNode.common_stage

/-- The complete original first target Request remains the SAME retained shape/attempt/checking cache. -/
theorem firstRequested_request
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    :
    HEq (firstRequested (following := following) firstNode).request firstNode.next.requested.request :=
  (firstNode.common.requested.castAccuracy_request
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm).trans
      firstNode.common_request

/-- The whole original first target preparation remains the SAME globally allocated model/query product. -/
theorem firstRequested_prepared
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    :
    HEq (firstRequested (following := following) firstNode).prepared firstNode.next.requested.prepared :=
  firstNode.common.requested.castAccuracy_prepared_trans
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
      firstNode.common_prepared

/-- The first accuracy view reads the literal original programme model at every actual stage. -/
theorem firstRequested_model
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    (firstPrograms : ValueBlocks
    (source := firstNode.paid.1) (next := firstNode.next)
    (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positive direction moving)))
    (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (channel : Fin 6) (stage : Nat) :
    (firstRequested (following := following) firstNode).modelAt
      (parameter := parameter) (increment := Sampling.gridOffset intervals index.succ direction)
      (target := firstNode.target) (basis := basis) (count := count) channel stage =
    ((firstPrograms.targetProgram (next := firstNode.next) channel).model stage) :=
  (firstNode.common.requested.castAccuracy_model
    (parameter := parameter) (increment := Sampling.gridOffset intervals index.succ direction)
    (target := firstNode.target) (basis := basis) (count := count)
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
    channel stage).trans
      ((firstNode.common.requested.modelAt_eq
        (parameter := parameter) (increment := Sampling.gridOffset intervals index.succ direction)
        (target := firstNode.target) (basis := basis) (count := count) channel stage).trans
        (firstNode.common_model_eq_program firstPrograms channel stage))

/-- The first selected model sample is the SAME literal original programme sample at its own selected stage. -/
theorem firstRequested_sample
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage : Nat}
    (firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage)
    (firstPrograms : ValueBlocks
    (source := firstNode.paid.1) (next := firstNode.next)
    (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positive direction moving)))
    (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (channel : Fin 6) :
    ((firstRequested (following := following) firstNode).modelAt
      (parameter := parameter) (increment := Sampling.gridOffset intervals index.succ direction)
      (target := firstNode.target) (basis := basis) (count := count) channel
      (firstRequested (following := following) firstNode).selected.stage).integralSample =
    ((firstPrograms.targetProgram (next := firstNode.next) channel).model
      firstNode.next.requested.selected.stage).integralSample :=
  congrArg (fun original : PathModel => original.integralSample)
    ((firstRequested_model (following := following) firstNode firstPrograms channel
      (firstRequested (following := following) firstNode).selected.stage).trans
      (congrArg (fun stage => (firstPrograms.targetProgram (next := firstNode.next) channel).model stage)
        (firstRequested_stage (following := following) firstNode)))

end First

section Last

/-- Read the SAME whole last target Request at the exactly equal actual local-difference accuracy index. -/
@[expose] def lastRequested
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    : lastNode.common.requested.AtAccuracy
    (spatial.minimum (Sampling.incrementRequest (Sampling.gridPositiveIncrement intervals index following direction)
        (Sampling.gridPositiveDifference_nonzero intervals positive index following direction moving))) :=
  ShiftedGeometry.Requested.castAccuracy
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
    lastNode.common.requested

/-- The whole original last target Requested cache is retained by this exact accuracy view. -/
theorem lastRequested_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    : HEq (lastRequested (following := following) lastNode) lastNode.common.requested :=
  lastNode.common.requested.castAccuracy_heq
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm

/-- The actual selected last target stage is unchanged and remains its literal original programme stage. -/
theorem lastRequested_stage
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    :
    (lastRequested (following := following) lastNode).selected.stage = lastNode.next.requested.selected.stage :=
  (lastNode.common.requested.castAccuracy_stage
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm).trans
      lastNode.common_stage

/-- The complete original last target Request remains the SAME retained shape/attempt/checking cache. -/
theorem lastRequested_request
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    :
    HEq (lastRequested (following := following) lastNode).request lastNode.next.requested.request :=
  (lastNode.common.requested.castAccuracy_request
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm).trans
      lastNode.common_request

/-- The whole original last target preparation remains the SAME globally allocated model/query product. -/
theorem lastRequested_prepared
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    :
    HEq (lastRequested (following := following) lastNode).prepared lastNode.next.requested.prepared :=
  lastNode.common.requested.castAccuracy_prepared_trans
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
      lastNode.common_prepared

/-- The last accuracy view reads the literal original programme model at every actual stage. -/
theorem lastRequested_model
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    (lastPrograms : ValueBlocks
    (source := lastNode.paid.1) (next := lastNode.next)
    (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positive direction moving)))
    (nonzero := Sampling.gridOffset_nonzero intervals positive
      (Sampling.gridNextIndex intervals index following) direction moving))
    (channel : Fin 6) (stage : Nat) :
    (lastRequested (following := following) lastNode).modelAt
      (parameter := parameter) (increment := Sampling.gridOffset intervals
        (Sampling.gridNextIndex intervals index following).succ direction)
      (target := lastNode.target) (basis := basis) (count := count) channel stage =
    ((lastPrograms.targetProgram (next := lastNode.next) channel).model stage) :=
  (lastNode.common.requested.castAccuracy_model
    (parameter := parameter) (increment := Sampling.gridOffset intervals
      (Sampling.gridNextIndex intervals index following).succ direction)
    (target := lastNode.target) (basis := basis) (count := count)
    (Sampling.gridPositiveRequest_eq intervals positive index following direction moving spatial).symm
    channel stage).trans
      ((lastNode.common.requested.modelAt_eq
        (parameter := parameter) (increment := Sampling.gridOffset intervals
          (Sampling.gridNextIndex intervals index following).succ direction)
        (target := lastNode.target) (basis := basis) (count := count) channel stage).trans
        (lastNode.common_model_eq_program lastPrograms channel stage))

/-- The last selected model sample is the SAME literal original programme sample at its own selected stage. -/
theorem lastRequested_sample
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {lastCurrent lastFloor lastRootStage : Nat}
    (lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage)
    (lastPrograms : ValueBlocks
    (source := lastNode.paid.1) (next := lastNode.next)
    (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positive direction moving)))
    (nonzero := Sampling.gridOffset_nonzero intervals positive
      (Sampling.gridNextIndex intervals index following) direction moving))
    (channel : Fin 6) :
    ((lastRequested (following := following) lastNode).modelAt
      (parameter := parameter) (increment := Sampling.gridOffset intervals
        (Sampling.gridNextIndex intervals index following).succ direction)
      (target := lastNode.target) (basis := basis) (count := count) channel
      (lastRequested (following := following) lastNode).selected.stage).integralSample =
    ((lastPrograms.targetProgram (next := lastNode.next) channel).model
      lastNode.next.requested.selected.stage).integralSample :=
  congrArg (fun original : PathModel => original.integralSample)
    ((lastRequested_model (following := following) lastNode lastPrograms channel
      (lastRequested (following := following) lastNode).selected.stage).trans
      (congrArg (fun stage => (lastPrograms.targetProgram (next := lastNode.next) channel).model stage)
        (lastRequested_stage (following := following) lastNode)))

end Last

section StoredRows

/-- The exact existing global row-cache type at these two actual positive-node request views.

This is only the original BetweenRows application. Every old source, node,
Request, global occurrence, Alignment, pair, restriction and Sample cache
remains an index or retained entry. No data is created by this type alias.
-/
@[expose] def AdjacentRows
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage}
    {lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage}
    {unit : Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals index following direction) ≤ 1}
    {firstPositions : Position.Family firstNode.common.blocks
      (firstRequested (following := following) firstNode).request}
    {lastPositions : Position.Family lastNode.common.blocks
      (lastRequested (following := following) lastNode).request}
    {firstAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.firstReference)}
    := BetweenRows source.prepared ranges allocation
  ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
  ((Sampling.gridOffset_normSq_le intervals positive
    (Sampling.gridNextIndex intervals index following).succ direction).trans admitted)
  firstWidths lastWidths firstNode.common.blocks lastNode.common.blocks unit
  (Sampling.gridPositiveDifference_nonzero intervals positive index following direction moving) spatial
  (firstRequested (following := following) firstNode) (lastRequested (following := following) lastNode)
  firstPositions lastPositions firstAligned lastAligned

/-- Exact quantified base-programme readback on the two retained nodes and their stored rows. -/
abbrev BaseReadback : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage}
    {lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage}
    {unit : Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals index following direction) ≤ 1}
    {firstPositions : Position.Family firstNode.common.blocks
      (firstRequested (following := following) firstNode).request}
    {lastPositions : Position.Family lastNode.common.blocks
      (lastRequested (following := following) lastNode).request}
    {firstAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.firstReference)}
    {rows : AdjacentRows (firstNode := firstNode) (lastNode := lastNode) (unit := unit)
      (firstPositions := firstPositions) (lastPositions := lastPositions)
      (firstAligned := firstAligned) (lastAligned := lastAligned)}
    (actual : BetweenRows.Integral rows)

    (firstPrograms : ValueBlocks
      (source := firstNode.paid.1) (next := firstNode.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).base =
    ((firstPrograms.targetProgram (next := firstNode.next) (Specification.Table.baseIndex order coordinate)).model
      firstNode.next.requested.selected.stage).integralSample

/-- The stored global base is the literal original first programme sample at its retained selected stage. -/
theorem base_program : BaseReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    index following direction moving spatial source member ranges allocation admitted root roots firstWidths
    lastWidths firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage firstNode lastNode
    unit firstPositions lastPositions firstAligned lastAligned rows actual firstPrograms order coordinate
  have original := actual.base firstNode.common.geometry_eq order coordinate
  have programme := firstRequested_sample (following := following) firstNode firstPrograms
    (Specification.Table.baseIndex order coordinate)
  exact original.trans programme

/-- Exact quantified output-programme readback on the two retained nodes and their stored rows. -/
abbrev OutputReadback : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage}
    {lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage}
    {unit : Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals index following direction) ≤ 1}
    {firstPositions : Position.Family firstNode.common.blocks
      (firstRequested (following := following) firstNode).request}
    {lastPositions : Position.Family lastNode.common.blocks
      (lastRequested (following := following) lastNode).request}
    {firstAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.firstReference)}
    {rows : AdjacentRows (firstNode := firstNode) (lastNode := lastNode) (unit := unit)
      (firstPositions := firstPositions) (lastPositions := lastPositions)
      (firstAligned := firstAligned) (lastAligned := lastAligned)}
    (actual : BetweenRows.Integral rows)

    (lastPrograms : ValueBlocks
      (source := lastNode.paid.1) (next := lastNode.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive
        (Sampling.gridNextIndex intervals index following) direction moving))
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).output =
    ((lastPrograms.targetProgram (next := lastNode.next) (Specification.Table.baseIndex order coordinate)).model
      lastNode.next.requested.selected.stage).integralSample

/-- The stored global output is the literal original last programme sample at its retained selected stage. -/
theorem output_program : OutputReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    index following direction moving spatial source member ranges allocation admitted root roots firstWidths
    lastWidths firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage firstNode lastNode
    unit firstPositions lastPositions firstAligned lastAligned rows actual lastPrograms order coordinate
  have original := actual.output lastNode.common.geometry_eq order coordinate
  have programme := lastRequested_sample (following := following) lastNode lastPrograms
    (Specification.Table.baseIndex order coordinate)
  exact original.trans programme

/-- Exact quantified slope-programme readback on the two retained nodes and their stored rows. -/
abbrev SlopeReadback : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage}
    {lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage}
    {unit : Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals index following direction) ≤ 1}
    {firstPositions : Position.Family firstNode.common.blocks
      (firstRequested (following := following) firstNode).request}
    {lastPositions : Position.Family lastNode.common.blocks
      (lastRequested (following := following) lastNode).request}
    {firstAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.firstReference)}
    {rows : AdjacentRows (firstNode := firstNode) (lastNode := lastNode) (unit := unit)
      (firstPositions := firstPositions) (lastPositions := lastPositions)
      (firstAligned := firstAligned) (lastAligned := lastAligned)}
    (actual : BetweenRows.Integral rows)

    (firstPrograms : ValueBlocks
      (source := firstNode.paid.1) (next := firstNode.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).slope =
    ((firstPrograms.targetProgram (next := firstNode.next) (Specification.Table.slopeIndex order coordinate)).model
      firstNode.next.requested.selected.stage).integralSample

/-- The stored global slope is the literal original first programme sample at its retained selected stage. -/
theorem slope_program : SlopeReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    index following direction moving spatial source member ranges allocation admitted root roots firstWidths
    lastWidths firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage firstNode lastNode
    unit firstPositions lastPositions firstAligned lastAligned rows actual firstPrograms order coordinate
  have original := actual.slope firstNode.common.geometry_eq order coordinate
  have programme := firstRequested_sample (following := following) firstNode firstPrograms
    (Specification.Table.slopeIndex order coordinate)
  exact original.trans programme

-- Retain the original named integral witness, whose existence supplies the bound.
set_option linter.unusedVariables false in
/-- Exact quantified programme residual bound on both retained nodes and their original integral rows. -/
abbrev RemainderBound : Prop :=
  ∀ {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {index : Fin intervals} {following : index.val + 1 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstNode : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted firstWidths roots firstCurrent firstFloor firstRootStage}
    {lastNode : PositiveGridNode intervals positive (Sampling.gridNextIndex intervals index following)
      direction moving spatial source member ranges allocation admitted lastWidths roots
      lastCurrent lastFloor lastRootStage}
    {unit : Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals index following direction) ≤ 1}
    {firstPositions : Position.Family firstNode.common.blocks
      (firstRequested (following := following) firstNode).request}
    {lastPositions : Position.Family lastNode.common.blocks
      (lastRequested (following := following) lastNode).request}
    {firstAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) firstNode.common.blocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) lastNode.common.blocks outer).comparison.firstReference)}
    {rows : AdjacentRows (firstNode := firstNode) (lastNode := lastNode) (unit := unit)
      (firstPositions := firstPositions) (lastPositions := lastPositions)
      (firstAligned := firstAligned) (lastAligned := lastAligned)}
    (actual : BetweenRows.Integral rows)

    (firstPrograms : ValueBlocks
      (source := firstNode.paid.1) (next := firstNode.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (lastPrograms : ValueBlocks
      (source := lastNode.paid.1) (next := lastNode.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive
        (Sampling.gridNextIndex intervals index following) direction moving))
    (order coordinate : Fin 2),
    Canonical.normSq
      (((lastPrograms.targetProgram (next := lastNode.next) (Specification.Table.baseIndex order coordinate)).model
        lastNode.next.requested.selected.stage).integralSample -
      ((firstPrograms.targetProgram (next := firstNode.next) (Specification.Table.baseIndex order coordinate)).model
        firstNode.next.requested.selected.stage).integralSample -
      Sampling.gridPositiveIncrement intervals index following direction *
        ((firstPrograms.targetProgram (next := firstNode.next) (Specification.Table.slopeIndex order coordinate)).model
          firstNode.next.requested.selected.stage).integralSample) ≤
    ValueBlocks.factor (covered := covered) order coordinate *
      Canonical.normSq (Sampling.gridPositiveIncrement intervals index following direction) ^ 2

/-- All four SAME stored rows bound the residual of the two literal original target programme samples.

Only exact Request/model readbacks change the displayed owners. The original
global certificate, factor, expansion and remainder remain unchanged. No
new programme, target acquisition, row integral, Completion or final sample
comparison is constructed or supplied.
-/
theorem remainder_program_le : RemainderBound := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    index following direction moving spatial source member ranges allocation admitted root roots firstWidths
    lastWidths firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage firstNode lastNode
    unit firstPositions lastPositions firstAligned lastAligned rows actual firstPrograms lastPrograms order
    coordinate
  have difference := congrArg₂ (fun output base : Canonical => output - base)
    (output_program actual lastPrograms order coordinate) (base_program actual firstPrograms order coordinate)
  have residual := congrArg₂ (fun value slope : Canonical =>
    value - Sampling.gridPositiveIncrement intervals index following direction * slope)
      difference (slope_program actual firstPrograms order coordinate)
  have bounded := (congrArg Canonical.normSq
    (residual.symm.trans (actual.certificates order coordinate).expansion)).trans_le
      (actual.certificates order coordinate).remainder_le
  exact bounded.trans_eq (congrArg (fun factor : Rational =>
    factor * Canonical.normSq (Sampling.gridPositiveIncrement intervals index following direction) ^ 2)
      (actual.factor_eq order coordinate))

end StoredRows

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
