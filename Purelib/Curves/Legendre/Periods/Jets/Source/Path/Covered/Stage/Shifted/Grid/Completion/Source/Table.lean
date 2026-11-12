module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source.Table.Trace

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Euler
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Payment
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Trace
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Table
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries.Preparation
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment
import Purelib.Data.Vector.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Algebra.Recurrence.Affine
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms

/-! # Following Euler bounds and executions on retained sufficient-source tables -/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)
namespace PositiveGridNode.CompletionData.RequestedSource

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn)
open Purelib.Algebra.Recurrence
open Purelib.Calculus.Linear
open Purelib.LinearAlgebra.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

/-- The closed doubling multiplier used by both original coarse recurrences is nonnegative. -/
private theorem twoNonnegative : (0 : Rational) ≤ 2 := by decide +kernel


/-- The complete second-window error proposition on one actual retained incoming target.

The same original requested-source pair, reprepare operation, ranges,
allocation, widths, table, trace and completions remain in their literal
dependent order. The initial vector and scalar charge are indices; no
error estimate, geometry admission or replacement cache is supplied.
-/
@[expose] def EulerBound
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
    (initial : Data.Vector Canonical 2) (charge : Rational) : Prop :=
  let nextFrame := node.target
  let nextCount := coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let paid := incoming.requestedSource nextCurrent nextAccuracy
  let nextQueries : Queries node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent paid :=
    reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent paid incoming
  (nextRanges : Range node) →
  (nextAllocation : ParameterRange.StripAllocation nextRanges) →
  (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound) →
  (nextWidths : Fin
    (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest) →
  (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) →
  (table : Table node nextCount positiveCount nextDirection nextMoving nextSpatial nextCurrent
    paid nextRanges nextAllocation nextAdmitted nextWidths
    nextTargetCurrent nextTargetFloor nextTargetRootStage) →
  (trace : Table.Trace table) →
  (completions : Table.Completions table nextQueries) →
  Table.Trace.EulerBound
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (node := node) (nextIntervals := nextCount) (nextPositive := positiveCount)
    (nextDirection := nextDirection) (nextMoving := nextMoving) (nextSpatial := nextSpatial)
    (nextCurrent := nextCurrent) (paid := paid) (nextRanges := nextRanges)
    (nextAllocation := nextAllocation) (nextAdmitted := nextAdmitted) (nextWidths := nextWidths)
    (nextTargetCurrent := nextTargetCurrent) (nextTargetFloor := nextTargetFloor)
    (nextTargetRootStage := nextTargetRootStage) (table := table)
    trace nextRefinement initial charge

/-- The complete second-window Euler-result type on one actual retained incoming target.

The same original requested-source pair, reprepare operation, ranges,
allocation, widths, table, trace and completions remain in their literal
dependent order. The initial vector and scalar charge are indices; no
error estimate, geometry admission or replacement cache is supplied.
-/
@[expose] def EulerResult
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
    (initial : Data.Vector Canonical 2) (charge : Rational) : Type _ :=
  let nextFrame := node.target
  let nextCount := coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let paid := incoming.requestedSource nextCurrent nextAccuracy
  let nextQueries : Queries node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent paid :=
    reprepare node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent paid incoming
  (nextRanges : Range node) →
  (nextAllocation : ParameterRange.StripAllocation nextRanges) →
  (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound) →
  (nextWidths : Fin
    (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest) →
  (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) →
  (table : Table node nextCount positiveCount nextDirection nextMoving nextSpatial nextCurrent
    paid nextRanges nextAllocation nextAdmitted nextWidths
    nextTargetCurrent nextTargetFloor nextTargetRootStage) →
  (trace : Table.Trace table) →
  (completions : Table.Completions table nextQueries) →
  Table.Trace.EulerResult
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (node := node) (nextIntervals := nextCount) (nextPositive := positiveCount)
    (nextDirection := nextDirection) (nextMoving := nextMoving) (nextSpatial := nextSpatial)
    (nextCurrent := nextCurrent) (paid := paid) (nextRanges := nextRanges)
    (nextAllocation := nextAllocation) (nextAdmitted := nextAdmitted) (nextWidths := nextWidths)
    (nextTargetCurrent := nextTargetCurrent) (nextTargetFloor := nextTargetFloor)
    (nextTargetRootStage := nextTargetRootStage) (table := table)
    trace nextRefinement initial charge

/-- The complete second-window Euler estimate for every retained request and incoming vector.

The statement retains the original sufficient source, transported queries,
table, trace and Completion caches. Its scalar charge pays the actual
incoming discrepancy and the same original affine recurrence.
-/
@[expose] def EulerBoundLaw : Prop :=
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
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (initial : Data.Vector Canonical 2) (tolerance : Rational)
    (_initialError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
          node.next.requested.selected.stage).integralSample)) initial) ≤ tolerance),
    EulerBound
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old)
      incoming nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial
      (2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
        node.next.requested.selected.stage + tolerance))

/-- The retained target programme pays the entire following-window Euler bound from its actual incoming error.

The same CompletionData produces its requested source and reuses its
query operation. The old selected programme sample is compared with that
new source internally, then its proved incoming discrepancy is propagated
through the original affine recurrence. The conclusion quantifies over
actual admitted ranges, tables, traces and completions; no following
sample bound, replacement preparation or geometric admission is input.
-/
theorem eulerBound : EulerBoundLaw := by
  unfold EulerBoundLaw
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old incoming programmes nextDirection nextMoving
    nextSpatial nextCurrent nextRefinement nextPositive initial tolerance initialError
  dsimp only [EulerBound]
  intro nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace completions
  let nextFrame := node.target
  let nextCount := coarseIntervals nextFrame nextDirection * nextRefinement
  let positiveCount := fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
  let nextAccuracy := (connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
      (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
  let paid := incoming.requestedSource nextCurrent nextAccuracy
  let nextQueries : Queries node nextCount positiveCount nextDirection nextMoving
      nextSpatial nextCurrent paid :=
    reprepare node nextCount positiveCount nextDirection nextMoving nextSpatial nextCurrent paid incoming
  let fineWidth : Rational := 1 / (nextCount : Rational)
  let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
    ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
    Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
  let forcing := 2 * ((nextRefinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
  let radius := Geometric.Basic.quarterRadius (errorScale (parent :: parents)) node.next.requested.selected.stage
  have handoff := incoming.requested_initial_iterate_le programmes nextCurrent nextAccuracy initial
    forcing (coarseIntervals nextFrame nextDirection)
  dsimp only at handoff
  have scalar := mul_le_mul_of_nonneg_left_direct
    (add_le_add_direct (Data.Rat.Fraction.Order.Basic.le_refl (2 * radius)) initialError)
    twoNonnegative
  have propagated := Affine.comparison (fun _ => (2 : Rational)) (fun _ => forcing)
    (Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing)
      (2 * (2 * radius + Norm.vector (zipWith (fun sample approximate => sample - approximate)
        (vectorOfFn (fun coordinate =>
          ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
            node.next.requested.selected.stage).integralSample)) initial)))) (2 * (2 * radius + tolerance))
    (coarseIntervals nextFrame nextDirection) scalar
    (fun _ _ => twoNonnegative) (fun _ _ => Data.Rat.Fraction.Order.Basic.le_refl _)
  have payment := handoff.trans propagated
  exact Table.Trace.eulerBlocks_from_source_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage)
    (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
    (spatial := spatial) (source := source) (member := member)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (index := index)
    node nextRefinement nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
    nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace nextQueries completions initial (2 * (2 * radius + tolerance)) payment

/-- Execute one following Euler trace from the actual incoming vector with its internally derived whole-window bound.

The same incoming CompletionData, old target programme and initial error
certificate establish the existing quantified EulerResult. Each admitted
window retains its literal source, query, table, trace and completions;
the original fixed-trace constructor executes Euler.trace once. No final
bound, replacement sample or new geometric admission is an input.
-/
def eulerResult
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
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (initial : Data.Vector Canonical 2) (tolerance : Rational)
    (initialError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
          node.next.requested.selected.stage).integralSample)) initial) ≤ tolerance) :
    EulerResult
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      (node := node) (aligned := aligned) (alignedEq := alignedEq) (old := old)
      incoming nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial
      (2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
        node.next.requested.selected.stage + tolerance)) := by
  dsimp only [EulerResult]
  intro nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace completions
  exact Table.Trace.EulerResult.ofBound
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage)
    (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
    (spatial := spatial) (source := source) (member := member)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (index := index)
    (node := node)
    (nextDirection := nextDirection) (nextMoving := nextMoving) (nextSpatial := nextSpatial)
    (nextCurrent := nextCurrent) (nextRanges := nextRanges) (nextAllocation := nextAllocation)
    (nextAdmitted := nextAdmitted) (nextWidths := nextWidths)
    (nextTargetCurrent := nextTargetCurrent) (nextTargetFloor := nextTargetFloor)
    (nextTargetRootStage := nextTargetRootStage) (table := table)
    trace nextRefinement initial
    (2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
      node.next.requested.selected.stage + tolerance))
    (eulerBound
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      node (aligned := aligned) (alignedEq := alignedEq) (old := old)
      incoming programmes nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      initial tolerance initialError
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
      table trace completions)

/-- The exact whole-factory equation for every retained second-window Euler execution.

The statement retains the original requested source, geometry, table, trace
and Completion caches in their dependent order. It identifies the complete
Euler result with its original factory and bound witnesses.
-/
@[expose] def EulerResultEquation : Prop :=
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
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (initial : Data.Vector Canonical 2) (tolerance : Rational)
    (initialError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
          node.next.requested.selected.stage).integralSample)) initial) ≤ tolerance),
    let nextFrame := node.target
    let nextCount := coarseIntervals nextFrame nextDirection * nextRefinement
    let positiveCount := fineIntervals_positive nextFrame nextDirection nextRefinement nextPositive
    let nextAccuracy := (connectionRequest nextFrame nextCount positiveCount nextSpatial).minimum
      (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
        (Sampling.gridIncrement_nonzero nextCount positiveCount nextDirection nextMoving))
    let paid := incoming.requestedSource nextCurrent nextAccuracy
    let nextQueries : Queries node nextCount positiveCount nextDirection nextMoving
        nextSpatial nextCurrent paid :=
      reprepare node nextCount positiveCount nextDirection nextMoving
        nextSpatial nextCurrent paid incoming
    (nextRanges : Range node) →
    (nextAllocation : ParameterRange.StripAllocation nextRanges) →
    (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound) →
    (nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest) →
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) →
    (table : Table node nextCount positiveCount nextDirection nextMoving nextSpatial nextCurrent
      paid nextRanges nextAllocation nextAdmitted nextWidths
      nextTargetCurrent nextTargetFloor nextTargetRootStage) →
    (trace : Table.Trace table) →
    (completions : Table.Completions table nextQueries) →
    eulerResult
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
      (spatial := spatial) (source := source) (member := member)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (index := index)
      node (aligned := aligned) (alignedEq := alignedEq) (old := old)
      incoming programmes nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
      initial tolerance initialError
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
      table trace completions =
    let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
    let boundedIndex := fun position : Nat => (⟨min position nextCount,
      Nat.lt_succ_of_le (Nat.min_le_right position nextCount)⟩ : Fin (nextCount + 1))
    let coefficients := fun position => Jets.Connection.alongMatrix
      (nextParameter + Sampling.gridOffset nextCount (boundedIndex position) nextDirection) nextDirection
    let fineWidth : Rational := 1 / (nextCount : Rational)
    let values := Euler.trace coefficients (fun _ => fineWidth) initial nextCount
    (⟨values, rfl,
      eulerBound
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage)
        (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
        (spatial := spatial) (source := source) (member := member)
        (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
        (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (index := index)
        node (aligned := aligned) (alignedEq := alignedEq) (old := old)
        incoming programmes nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
        initial tolerance initialError
        nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
        table trace completions⟩ :
      Table.Trace.EulerResult
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage)
        (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
        (spatial := spatial) (source := source) (member := member)
        (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
        (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (index := index)
        (node := node)
        (nextDirection := nextDirection) (nextMoving := nextMoving) (nextSpatial := nextSpatial)
        (nextCurrent := nextCurrent) (nextRanges := nextRanges) (nextAllocation := nextAllocation)
        (nextAdmitted := nextAdmitted) (nextWidths := nextWidths)
        (nextTargetCurrent := nextTargetCurrent) (nextTargetFloor := nextTargetFloor)
        (nextTargetRootStage := nextTargetRootStage) (table := table)
        trace nextRefinement initial (2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
          node.next.requested.selected.stage + tolerance)))

/-- At each actual admitted window the complete result is its single Euler execution and the same derived bound.

This is an equality of the returned certified vector after all original
window caches have been supplied. Its right side retains the exact trace
factory equality and eulerBound witness; it compares no functions and
requires no body exposure or source/cache reconstruction by a caller.
-/
theorem eulerResult_eq : EulerResultEquation := by
  unfold EulerResultEquation
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old incoming programmes nextDirection nextMoving
    nextSpatial nextCurrent nextRefinement nextPositive initial tolerance initialError
  dsimp only
  intro nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace completions
  unfold eulerResult
  exact Table.Trace.EulerResult.ofBound_eq _ _ _ _ _

end PositiveGridNode.CompletionData.RequestedSource
end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
