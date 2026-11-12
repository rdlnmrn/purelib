module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Euler
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
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms

/-! # Exact table, query and sample families on one original sufficient source

The original node fixes its target frame, covered parents, chain and stage.
One retained RequestedSource pair supplies the same request/member to the
original nominal Table. The aliases keep all source/target indices explicit
at generic original node indices. The query operation delegates to the
original reprepare on that same pair and retained incoming CompletionData.
-/

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

/-- The exact original whole-cover range family on the same actual target node.

The complete target frame, displayed parameter, differential and parent
indices are fixed inside this type alias. Its values remain the original
ParameterRange caches and their complete factory predicates.
-/
@[expose] def Range
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
    : Type _ :=
  ParameterRange
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parents := node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2)
    node.next.requested.request.covered

section

variable
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

namespace Range

/-- The original strip allocation on this actual node's whole retained target range.

The exact type retains the target frame, covered-parent indices and
original range value. It adds no owner or allocation computation.
-/
@[expose] def Allocation (ranges : Range node) : Type _ := ParameterRange.StripAllocation ranges

/-- The original squared-increment admission for this node's complete retained strip allocation.

This exact proposition keeps the original range, allocation and increment
as indices without expanding their covered-parent shape in client binders.
-/
@[expose] def Admission (ranges : Range node) (allocation : Allocation node ranges)
    (nextDirection : Canonical) : Prop := Norm.Basic.normSq nextDirection ≤ allocation.bound

end Range

/-- The original width-request family indexed by this actual node's retained target-parent occurrences.

The entire original parent shape fixes the finite index. Repeated parent
occurrences remain distinct and no width request is selected here.
-/
@[expose] def Widths : Type _ :=
  Fin (node.next.requested.request.shape.val.1 :: node.next.requested.request.shape.val.2).length → AccuracyRequest

variable
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

/-- The actual query-operation type on this SAME sufficient source preparation. -/
@[expose] def Queries : Type _ := QueryAgreement paid.1.prepared

variable
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}

/-- Transport the retained incoming query operation to this SAME already selected sufficient-source pair.

The original QueryAgreement.reprepare receives the literal old preparation,
new preparation and stored sourceQueries. No sufficient-source selection,
preparation, bank check or query observation runs when this callback is
constructed. Its original per-invocation observation behavior is retained.
-/
def reprepare (retained : CompletionData node aligned alignedEq old) :
    Queries node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid :=
  QueryAgreement.reprepare node.next.requested.asSource.prepared paid.1.prepared retained.sourceQueries

/-- The original nominal target table on this SAME request/member and literal retained parent geometry.

The whole original source indices, numerical floors and target indices
are fixed inside this alias. Its root chain is the existing geometry's
chain transported by the same Request.shape.property; no root is acquired.
-/
@[expose] def Table : Type _ :=
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  PositiveGridNode.Table
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    nextIntervals nextPositive nextDirection nextMoving
    (connectionRequest node.target nextIntervals nextPositive nextSpatial) paid.1 paid.2
    nextRanges nextAllocation nextAdmitted nextWidths nextRoots
    nextTargetCurrent nextTargetFloor nextTargetRootStage

namespace Table

variable {node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
    nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage}
    (table : Table node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid
      nextRanges nextAllocation nextAdmitted nextWidths nextTargetCurrent nextTargetFloor nextTargetRootStage)

/-- The original sample/certificate Trace family on this SAME nominal table. -/
@[expose] def Trace : Type _ :=
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  PositiveGridNode.Table.Trace
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    (intervals := nextIntervals) (positive := nextPositive) (direction := nextDirection) (moving := nextMoving)
    (spatial := connectionRequest node.target nextIntervals nextPositive nextSpatial)
    (source := paid.1) (member := paid.2) (ranges := nextRanges) (allocation := nextAllocation)
    (admitted := nextAdmitted) (widths := nextWidths) (roots := nextRoots)
    (targetCurrent := nextTargetCurrent) (targetFloor := nextTargetFloor)
    (targetRootStage := nextTargetRootStage) table

/-- The original ordered CompletionData vector on this SAME table and sufficient-source query operation. -/
@[expose] def Completions
    (queries : Queries node nextIntervals nextPositive nextDirection nextMoving
      nextSpatial nextCurrent paid) : Type _ :=
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  PositiveGridNode.Table.Completions
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    (intervals := nextIntervals) (positive := nextPositive) (direction := nextDirection) (moving := nextMoving)
    (spatial := connectionRequest node.target nextIntervals nextPositive nextSpatial)
    (source := paid.1) (member := paid.2) (ranges := nextRanges) (allocation := nextAllocation)
    (admitted := nextAdmitted) (widths := nextWidths) (roots := nextRoots)
    (targetCurrent := nextTargetCurrent) (targetFloor := nextTargetFloor)
    (targetRootStage := nextTargetRootStage) table queries

namespace Trace

variable {table}

/-- Read the original two-channel sample vector on this same table at its literal bounded index.

The original Trace.eulerValues reads the retained programmes and samples.
This body is exposed so clients can compare that same original operation
without inferring its complete dependent table family again.
-/
@[expose] def eulerValues (trace : Trace table) (position : Fin (nextIntervals + 1)) : Data.Vector Canonical 2 :=
  let nextRoots := PreparedBankRootChains.RootChain.castChildren
    node.next.requested.request.shape.property node.next.geometry.roots
  PositiveGridNode.Table.Trace.eulerValues
    (parameter := parameter + Sampling.gridOffset intervals index.succ direction)
    (frame := node.target) (basis := basis) (count := count)
    (parent := node.next.requested.request.shape.val.1)
    (parents := node.next.requested.request.shape.val.2)
    (covered := node.next.requested.request.covered) (chain := node.next.requested.request.chain)
    (current := max nextCurrent (node.next.requested.selected.stage + 1))
    (floor := targetFloor) (rootStage := targetRootStage)
    (intervals := nextIntervals) (positive := nextPositive) (direction := nextDirection) (moving := nextMoving)
    (spatial := nextSpatial) (source := paid.1) (member := paid.2)
    (ranges := nextRanges) (allocation := nextAllocation) (admitted := nextAdmitted) (widths := nextWidths)
    (roots := nextRoots) (targetCurrent := nextTargetCurrent) (targetFloor := nextTargetFloor)
    (targetRootStage := nextTargetRootStage) (table := table) trace position

end Trace

end Table

end

/-- The exact whole-callback transport equation for every retained source and query operation.

Both actual prepared owners, the sufficient-source pair and the incoming
stored query operation remain in their original dependent order. The law
compares the complete transported callback with the original reprepare.
-/
@[expose] def ReprepareEquation : Prop :=
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
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    (node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (nextIntervals : Nat) (nextPositive : 0 < nextIntervals)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent : Nat)
    (paid : RequestedSource node nextCurrent
      ((connectionRequest node.target nextIntervals nextPositive nextSpatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement nextIntervals nextDirection)
          (Sampling.gridIncrement_nonzero nextIntervals nextPositive nextDirection nextMoving))))
    {aligned : DependentProduct (parent :: parents) (fun outer => RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old),
    reprepare node nextIntervals nextPositive nextDirection nextMoving nextSpatial nextCurrent paid retained =
      QueryAgreement.reprepare node.next.requested.asSource.prepared paid.1.prepared retained.sourceQueries

/-- The whole transported callback is the original reprepare on both actual prepared owners and stored queries. -/
theorem reprepare_eq : ReprepareEquation := by
  unfold ReprepareEquation
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node nextIntervals nextPositive nextDirection nextMoving nextSpatial
    nextCurrent paid aligned alignedEq old retained
  rfl

end PositiveGridNode.CompletionData.RequestedSource
end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
