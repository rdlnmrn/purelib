module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source.Table.Data

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

/-! # Euler bounds and results on the retained sufficient-source trace -/

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

namespace Table.Trace

/-- The original terminal Euler-error proposition on the same trace and actual incoming vector.

All coefficients, sample indices, widths and forcing are the original
expressions on this retained table. The scalar charge is an index of the
proposition, not a supplied proof of any error estimate.
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
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {nextIntervals : Nat} {nextPositive : 0 < nextIntervals}
    {nextDirection : Canonical} {nextMoving : nextDirection ≠ 0}
    {nextSpatial : AccuracyRequest} {nextCurrent : Nat}
    {paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving)))}
    {nextRanges : Range node}
    {nextAllocation : ParameterRange.StripAllocation nextRanges}
    {nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound}
    {nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest}
    {nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat}
    {table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage}
    (trace : Trace table) (refinement : Nat) (initial : Data.Vector Canonical 2) (charge : Rational) : Prop :=
  let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
  let boundedIndex := fun position : Nat => (⟨min position nextIntervals,
    Nat.lt_succ_of_le (Nat.min_le_right position nextIntervals)⟩ : Fin (nextIntervals + 1))
  let coefficients := fun position => Jets.Connection.alongMatrix
    (nextParameter + Sampling.gridOffset nextIntervals (boundedIndex position) nextDirection) nextDirection
  let fineWidth : Rational := 1 / (nextIntervals : Rational)
  let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
    ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
    Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
  let forcing := 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
  Norm.vector (zipWith (fun sample approximate => sample - approximate)
    (eulerValues (table := table) trace ⟨nextIntervals, Nat.lt_succ_self nextIntervals⟩)
    (Euler.trace coefficients (fun _ => fineWidth) initial nextIntervals)) ≤
    Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing) charge
      (coarseIntervals node.target nextDirection)

/-- The original Euler vector subtype with its complete execution equality and terminal-error predicate.

The original trace starts at the actual supplied vector unchanged. The
returned type retains both its whole Euler equality and the same affine
bound on the same retained terminal sample; it introduces no new cache.
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
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {nextIntervals : Nat} {nextPositive : 0 < nextIntervals}
    {nextDirection : Canonical} {nextMoving : nextDirection ≠ 0}
    {nextSpatial : AccuracyRequest} {nextCurrent : Nat}
    {paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving)))}
    {nextRanges : Range node}
    {nextAllocation : ParameterRange.StripAllocation nextRanges}
    {nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound}
    {nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest}
    {nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat}
    {table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage}
    (trace : Trace table) (refinement : Nat) (initial : Data.Vector Canonical 2) (charge : Rational) : Type :=
  let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
  let boundedIndex := fun position : Nat => (⟨min position nextIntervals,
    Nat.lt_succ_of_le (Nat.min_le_right position nextIntervals)⟩ : Fin (nextIntervals + 1))
  let coefficients := fun position => Jets.Connection.alongMatrix
    (nextParameter + Sampling.gridOffset nextIntervals (boundedIndex position) nextDirection) nextDirection
  let fineWidth : Rational := 1 / (nextIntervals : Rational)
  let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
    ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
    Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
  let forcing := 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
  { values : Data.Vector Canonical 2 //
    values = Euler.trace coefficients (fun _ => fineWidth) initial nextIntervals ∧
    Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (eulerValues (table := table) trace ⟨nextIntervals, Nat.lt_succ_self nextIntervals⟩) values) ≤
      Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing) charge
        (coarseIntervals node.target nextDirection) }

/-- The same retained trace reads the original sufficient-source value channels at its initial node.

All source and target indices are fixed by the actual node and supplied
RequestedSource pair. This specializes the original trace readback
without selecting another source or constructing another preparation.
-/
theorem eulerValues_zero
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
    (nextIntervals : Nat) (nextPositive : 0 < nextIntervals)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent : Nat)
    (paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving))))
    (nextRanges : Range node)
    (nextAllocation : ParameterRange.StripAllocation nextRanges)
    (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound)
    (nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (trace : Trace table) :
    eulerValues (table := table) trace 0 = vectorOfFn (fun coordinate =>
      sourceSample paid.1 paid.2 (Specification.Table.valueIndex coordinate)) := by
  exact PositiveGridNode.Table.Trace.eulerValues_zero
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    (intervals := nextIntervals) (positive := nextPositive)
    (direction := nextDirection) (moving := nextMoving) (spatial := nextSpatial)
    (source := paid.1) (member := paid.2)
    (ranges := nextRanges) (allocation := nextAllocation) (admitted := nextAdmitted) (widths := nextWidths)
    (roots := PreparedBankRootChains.RootChain.castChildren
      node.next.requested.request.shape.property node.next.geometry.roots)
    (targetCurrent := nextTargetCurrent) (targetFloor := nextTargetFloor)
    (targetRootStage := nextTargetRootStage) (table := table) trace

/-- The original finite block estimate applies to this same retained sufficient-source table and trace.

The actual initial vector is propagated unchanged. Both query and
Completion caches are supplied on the same table; the conclusion is the
original affine error bound, including its actual initial discrepancy.
No source selection, observation, table or Euler execution is repeated.
-/
theorem eulerBlocks_from_le
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
    (nextRefinement : Nat) (nextRefinementPositive : 0 < nextRefinement)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent : Nat)
    (paid :
      let nextCount := coarseIntervals node.target nextDirection * nextRefinement
      let nextPositive := fineIntervals_positive node.target nextDirection nextRefinement nextRefinementPositive
      RequestedSource node nextCurrent
        ((connectionRequest node.target nextCount nextPositive nextSpatial).minimum
          (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
            (Sampling.gridIncrement_nonzero nextCount nextPositive nextDirection nextMoving))))
    (nextRanges : Range node)
    (nextAllocation : ParameterRange.StripAllocation nextRanges)
    (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound)
    (nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) :
    let nextCount := coarseIntervals node.target nextDirection * nextRefinement
    let nextPositive := fineIntervals_positive node.target nextDirection nextRefinement nextRefinementPositive
    (table : Table node nextCount nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage) →
    (trace : Trace table) →
    (queries : Queries node nextCount nextPositive nextDirection nextMoving nextSpatial nextCurrent paid) →
    (completions : Completions table queries) →
    (initial : Data.Vector Canonical 2) →
    let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
    let boundedIndex := fun position : Nat => (⟨min position nextCount,
      Nat.lt_succ_of_le (Nat.min_le_right position nextCount)⟩ : Fin (nextCount + 1))
    let coefficients := fun position => Jets.Connection.alongMatrix
      (nextParameter + Sampling.gridOffset nextCount (boundedIndex position) nextDirection) nextDirection
    let fineWidth : Rational := 1 / (nextCount : Rational)
    let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
      ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
      Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
    Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (eulerValues (table := table) trace ⟨nextCount, Nat.lt_succ_self nextCount⟩)
      (Euler.trace coefficients (fun _ => fineWidth) initial nextCount)) ≤
      Affine.iterate (fun _ => (2 : Rational))
        (fun _ => 2 * ((nextRefinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3)))
        (Norm.vector (zipWith (fun sample approximate => sample - approximate)
          (eulerValues (table := table) trace 0) initial))
        (coarseIntervals node.target nextDirection) := by
  dsimp only
  intro table trace queries completions initial
  exact PositiveGridNode.Table.Trace.eulerBlocks_from_le
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    (refinement := nextRefinement) (positiveRefinement := nextRefinementPositive)
    (direction := nextDirection) (moving := nextMoving) (spatial := nextSpatial)
    (source := paid.1) (member := paid.2)
    (ranges := nextRanges) (allocation := nextAllocation) (admitted := nextAdmitted) (widths := nextWidths)
    (roots := PreparedBankRootChains.RootChain.castChildren
      node.next.requested.request.shape.property node.next.geometry.roots)
    (targetCurrent := nextTargetCurrent) (targetFloor := nextTargetFloor)
    (targetRootStage := nextTargetRootStage) (table := table) trace queries completions initial

/-- The original block estimate follows a scalar affine payment from the same retained source samples.

The trace's initial-value readback and scalar payment transport the
original block estimate at the same generic owners. Query, completion,
source and Euler initial caches remain unchanged. The payment compares
only the original affine iterates; no final sample estimate is input.
-/
theorem eulerBlocks_from_source_le
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
    (nextRefinement : Nat) (nextRefinementPositive : 0 < nextRefinement)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent : Nat)
    (paid :
      let nextCount := coarseIntervals node.target nextDirection * nextRefinement
      let nextPositive := fineIntervals_positive node.target nextDirection nextRefinement nextRefinementPositive
      RequestedSource node nextCurrent
        ((connectionRequest node.target nextCount nextPositive nextSpatial).minimum
          (Sampling.incrementRequest (Sampling.gridIncrement nextCount nextDirection)
            (Sampling.gridIncrement_nonzero nextCount nextPositive nextDirection nextMoving))))
    (nextRanges : Range node)
    (nextAllocation : ParameterRange.StripAllocation nextRanges)
    (nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound)
    (nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat) :
    let nextCount := coarseIntervals node.target nextDirection * nextRefinement
    let nextPositive := fineIntervals_positive node.target nextDirection nextRefinement nextRefinementPositive
    (table : Table node nextCount nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage) →
    (trace : Trace table) →
    (queries : Queries node nextCount nextPositive nextDirection nextMoving nextSpatial nextCurrent paid) →
    (completions : Completions table queries) →
    (initial : Data.Vector Canonical 2) →
    (charge : Rational) →
    let fineWidth : Rational := 1 / (nextCount : Rational)
    let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
      ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
      Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
    let forcing := 2 * ((nextRefinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
    (payment : Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing)
      (Norm.vector (zipWith (fun sample approximate => sample - approximate)
        (vectorOfFn (fun coordinate => sourceSample paid.1 paid.2
          (Specification.Table.valueIndex coordinate))) initial))
      (coarseIntervals node.target nextDirection) ≤
      Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing) charge
        (coarseIntervals node.target nextDirection)) →
    EulerBound
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (node := node) (nextIntervals := nextCount) (nextPositive := nextPositive)
      (nextDirection := nextDirection) (nextMoving := nextMoving) (nextSpatial := nextSpatial)
      (nextCurrent := nextCurrent) (paid := paid) (nextRanges := nextRanges)
      (nextAllocation := nextAllocation) (nextAdmitted := nextAdmitted) (nextWidths := nextWidths)
      (nextTargetCurrent := nextTargetCurrent) (nextTargetFloor := nextTargetFloor)
      (nextTargetRootStage := nextTargetRootStage) (table := table)
      trace nextRefinement initial charge := by
  dsimp only
  intro table trace queries completions initial charge payment
  let nextCount := coarseIntervals node.target nextDirection * nextRefinement
  let nextPositive := fineIntervals_positive node.target nextDirection nextRefinement nextRefinementPositive
  let fineWidth : Rational := 1 / (nextCount : Rational)
  let factor := 2 * ((ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 0 +
    ShiftedGeometry.ValueBlocks.factor (covered := node.next.requested.request.covered) 0 1) *
    Norm.Basic.normSq nextDirection ^ 2 + 2 * Norm.Basic.normSq nextDirection)
  let forcing := 2 * ((nextRefinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
  have original := eulerBlocks_from_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage)
    (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
    (spatial := spatial) (source := source) (member := member)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (index := index)
    node nextRefinement nextRefinementPositive nextDirection nextMoving nextSpatial nextCurrent paid
    nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace queries completions initial
  dsimp only at original
  have sourceSample := eulerValues_zero
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage)
    (intervals := intervals) (positive := positive) (direction := direction) (moving := moving)
    (spatial := spatial) (source := source) (member := member)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (roots := roots) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (index := index)
    node nextCount nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
    nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage
    table trace
  have initialSample := congrArg (fun values : Data.Vector Canonical 2 => Norm.vector
    (zipWith (fun sample approximate => sample - approximate) values initial)) sourceSample
  have initialIterate := congrArg (fun value : Rational =>
    Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing) value
      (coarseIntervals node.target nextDirection)) initialSample
  have moved := original.trans_eq initialIterate
  exact moved.trans payment

namespace EulerResult

/-- Execute the original Euler trace once and retain its internally established fixed-trace bound.

The result keeps the same initial vector, coefficients, widths, trace
samples and complete EulerResult subtype. Its bound witness certifies this
exact execution; no source, table, observation or completion is rebuilt.
-/
def ofBound
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
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {nextIntervals : Nat} {nextPositive : 0 < nextIntervals}
    {nextDirection : Canonical} {nextMoving : nextDirection ≠ 0}
    {nextSpatial : AccuracyRequest} {nextCurrent : Nat}
    {paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving)))}
    {nextRanges : Range node}
    {nextAllocation : ParameterRange.StripAllocation nextRanges}
    {nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound}
    {nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest}
    {nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat}
    {table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage}
    (trace : Trace table) (refinement : Nat) (initial : Data.Vector Canonical 2) (charge : Rational)
    (bounded : EulerBound trace refinement initial charge) : EulerResult trace refinement initial charge :=
  let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
  let boundedIndex := fun position : Nat => (⟨min position nextIntervals,
    Nat.lt_succ_of_le (Nat.min_le_right position nextIntervals)⟩ : Fin (nextIntervals + 1))
  let coefficients := fun position => Jets.Connection.alongMatrix
    (nextParameter + Sampling.gridOffset nextIntervals (boundedIndex position) nextDirection) nextDirection
  let fineWidth : Rational := 1 / (nextIntervals : Rational)
  let values := Euler.trace coefficients (fun _ => fineWidth) initial nextIntervals
  ⟨values, rfl, bounded⟩

/-- The entire result is the same single Euler execution with its original equality and bound witnesses. -/
theorem ofBound_eq
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
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {nextIntervals : Nat} {nextPositive : 0 < nextIntervals}
    {nextDirection : Canonical} {nextMoving : nextDirection ≠ 0}
    {nextSpatial : AccuracyRequest} {nextCurrent : Nat}
    {paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving)))}
    {nextRanges : Range node}
    {nextAllocation : ParameterRange.StripAllocation nextRanges}
    {nextAdmitted : Norm.Basic.normSq nextDirection ≤ nextAllocation.bound}
    {nextWidths : Fin
      (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest}
    {nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat}
    {table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage}
    (trace : Trace table) (refinement : Nat) (initial : Data.Vector Canonical 2) (charge : Rational)
    (bounded : EulerBound trace refinement initial charge) :
    ofBound trace refinement initial charge bounded =
    let nextParameter := parameter + Sampling.gridOffset intervals index.succ direction
    let boundedIndex := fun position : Nat => (⟨min position nextIntervals,
      Nat.lt_succ_of_le (Nat.min_le_right position nextIntervals)⟩ : Fin (nextIntervals + 1))
    let coefficients := fun position => Jets.Connection.alongMatrix
      (nextParameter + Sampling.gridOffset nextIntervals (boundedIndex position) nextDirection) nextDirection
    let fineWidth : Rational := 1 / (nextIntervals : Rational)
    let values := Euler.trace coefficients (fun _ => fineWidth) initial nextIntervals
    (⟨values, rfl, bounded⟩ : EulerResult trace refinement initial charge) := by rfl

end EulerResult

end Table.Trace

end PositiveGridNode.CompletionData.RequestedSource
end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
