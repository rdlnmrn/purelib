module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Relations
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Following
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Euler
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Schedule
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries.Preparation
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.Algebra.Recurrence.Affine
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # A second retained Euler leg starts from the actual first computed endpoint

The literal first endpoint supplies its same source member, programmes and
all-query operation. A new sufficient member owns the second grid. The
original finite trace starts from the first computed vector unchanged;
its inherited programme discrepancy and original first accuracy payment
enter the derived affine bound. No requested-path existence or final
comparison is supplied, and no independently acquired frame is identified.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion.EulerExecution

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Completed)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open PositiveGridNode.CompletionData (RequestedSource)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Topology
open Purelib.LinearAlgebra.Gaussian
open Purelib.Algebra.Recurrence
open Purelib.Calculus.Linear
open Steps.Acquisition

/-- The exact dependent second-leg error proposition on the original retained incoming vector.

The same source request, query operation, actual table and trace remain
indices of the quantified conclusion. Its affine charge includes the
original first executor's paid discrepancy and tolerance; no comparison
or desired error is supplied as an additional premise.
-/
@[expose] def followingBound
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {direction : Canonical} {moving : direction ≠ 0} {request spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement) : Prop :=
  retained.grid.completions.FollowingBound retained.endpointIndex
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    retained.values
    (2 * (2 * Geometric.Basic.quarterRadius
      (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2))
      (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage + request.tolerance))

/-- The retained old target programme has the first executor's actual endpoint error at its unchanged selected stage.

The pointwise terminal sample readback identifies the same stored
programme vector with the actual first trace samples. Its existing paid
endpoint certificate bounds the discrepancy from retained.values; no
future-window request, geometry or desired error estimate is supplied.
-/
private theorem programme_error_le
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {direction : Canonical} {moving : direction ≠ 0} {request spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        (((retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
          (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
          (Jets.Specification.Table.valueIndex coordinate)).model
            (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage).integralSample))
      retained.values) ≤ request.tolerance := by
  let node := retained.grid.table.nodes.node retained.endpointIndex
  let programmes := retained.grid.table.programmes.entry retained.endpointIndex
  have previous_eq : vectorOfFn (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Jets.Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample) =
      retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩ := by
    apply vector_ext
    intro coordinate
    exact (vectorOfFn_apply (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Jets.Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample) coordinate).trans
          (retained.terminal_sample coordinate).symm
  have previousError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        ((programmes.targetProgram (next := node.next) (Jets.Specification.Table.valueIndex coordinate)).model
          node.next.requested.selected.stage).integralSample)) retained.values) ≤ request.tolerance :=
    (congrArg (fun values : Vec Canonical 2 => Norm.vector
      (zipWith (fun sample approximate => sample - approximate) values retained.values)) previous_eq).trans_le
        retained.endpoint_lt.le
  exact previousError

/-- The actual second retained grid propagates the first computed endpoint with its internally derived error.

The second sufficient source is exactly the original requested factory on
the first stored target Completion. Its own query operation is derived.
Only genuine second-window range/strip/width data and the actual retained
Table, Trace and Completions are supplied. Original sample readbacks and
the first executor's endpoint certificate pay the inherited discrepancy;
no initial equality, desired endpoint bound or right-frame identity is input.
-/
theorem followingEuler_le
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {direction : Canonical} {moving : direction ≠ 0} {request spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement) :
    followingBound retained nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive := by
  dsimp only [followingBound]
  exact retained.grid.completions.followingBound retained.endpointIndex
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    retained.values request.tolerance (programme_error_le retained)

/-- The exact retained second-leg result type on the original computed incoming vector.

The complete dependent function accepts the same admitted second-window
geometry and cached table, trace and completions. Its original Subtype
retains the actual Euler execution equality and the derived affine bound.
This alias introduces no data, factory or additional premise.
-/
@[expose] def FollowingResult
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {direction : Canonical} {moving : direction ≠ 0} {request spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement) : Type _ :=
  retained.grid.completions.FollowingResult retained.endpointIndex
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    retained.values
    (2 * (2 * Geometric.Basic.quarterRadius
      (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2))
      (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage + request.tolerance))

/-- Execute one actual second Euler trace from the same first computed vector, retaining factory and two-leg bound.

The original trace is called once on the supplied second cached grid.
The result is the existing vector/subtype owner with its exact execution
equality and derived affine estimate. No source/programme factory runs
inside this producer, and the first computed vector is never reset to a
period sample. This does not construct a prescribed full path or cycle
attachment from coordinate equality.
-/
def followingEuler
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {direction : Canonical} {moving : direction ≠ 0} {request spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement) :
    FollowingResult retained nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive := by
  dsimp only [FollowingResult]
  exact retained.grid.completions.followingResult retained.endpointIndex
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive
    retained.values request.tolerance (programme_error_le retained)

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion.EulerExecution
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
