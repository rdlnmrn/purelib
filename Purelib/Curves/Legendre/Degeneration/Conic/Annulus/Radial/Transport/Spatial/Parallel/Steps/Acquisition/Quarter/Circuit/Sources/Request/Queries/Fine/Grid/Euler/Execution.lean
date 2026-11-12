module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Schedule
import Purelib.Data.Vector.Basic
import Purelib.Data.Sigma.Factories

/-! # One requested finite Euler execution on the original completed fine cycle

Fixed coarse geometry chooses the original finite endpoint search before
fine acquisition. One literal original positive table, its completion
vector, one original trace cache and one original Euler trace are retained
with complete factory equalities and an internally proved endpoint bound.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted.PositiveGridNode

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.Periods
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (zipWith)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Calculus.Linear
open Purelib.LinearAlgebra.Gaussian
open Steps.Acquisition

namespace EulerExecution

section TraceTypes

variable
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
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    {intervals : Nat} {positive : 0 < intervals}
    (grid : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      (PositiveGridNode.connectionRequest frame intervals positive spatial) commonCurrent ranges allocation admitted
        widths targetCurrent targetFloor targetRootStage)

variable {completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage}

/-- The original trace carrier on this retained positive table. -/
@[expose] def TraceData : Type _ := Table.Trace grid.table

/-- The original whole trace factory equation on this same retained table. -/
@[expose] def TraceFactory (trace : TraceData (spatial := spatial) grid) : Prop := trace = Table.Trace.build grid.table

/-- The original trace and its complete factory equality, retained in the same subtype. -/
@[expose] def TraceCache : Type _ :=
  { trace : TraceData (spatial := spatial) grid // TraceFactory (spatial := spatial) grid trace }

/-- The original computed Euler vector and endpoint payment on the retained trace.

The coefficient schedule keeps the original parameter, direction and
bounded index. Both the initial and terminal vectors belong to this same
trace, and the original request pays the vector discrepancy.
-/
@[expose] def ValuesPredicate (trace : TraceData (spatial := spatial) grid) (values : Vec Canonical 2) : Prop :=
  let boundedIndex := fun index : Nat => (⟨min index intervals,
    Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
  let coefficients := fun index => Jets.Connection.alongMatrix
    (parameter + Sampling.gridOffset intervals (boundedIndex index) direction) direction
  values = Euler.trace coefficients (fun _ => 1 / (intervals : Rational))
    (Table.Trace.eulerValues (spatial := spatial) (table := grid.table) trace 0) intervals ∧
    Norm.vector (zipWith (fun first last => first - last)
      (Table.Trace.eulerValues (spatial := spatial) (table := grid.table) trace
        ⟨intervals, Nat.lt_succ_self intervals⟩) values) < request.tolerance

end TraceTypes

end EulerExecution

/-- The original finite endpoint selection, one actual completed grid, one trace cache and computed Euler result.

Only existing Sigma/Subtype containers are used. The selection is chosen
from fixed original geometry, its actual stage determines the positive
refinement, and that count determines the tighter request BEFORE the sole
positiveTable factory. The final certificate compares the computed vector
to the same literal terminal programme samples, retaining the whole cycle
and differential/source owners through the original grid.
-/
@[expose] def EulerExecution
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
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    :=
  (selection : { value : Search.Selection
      (Euler.endpointScale (PositiveGridNode.coarseIntervals frame direction)
        (PositiveGridNode.taylorFactor requested.covered direction)) 0 request.tolerance //
    value = Euler.endpointSelection (PositiveGridNode.coarseIntervals frame direction)
      (PositiveGridNode.taylorFactor requested.covered direction)
      (PositiveGridNode.taylorFactor_nonnegative requested.covered direction) request }) ×
  let refinement := 4 ^ selection.val.stage
  let fineCount := PositiveGridNode.coarseIntervals frame direction * refinement
  let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement (Nat.pow_pos (by decide))
  let paidSpatial := PositiveGridNode.connectionRequest frame fineCount positiveCount spatial
  (grid : { value : PositiveTable completed firstTen secondTen thirdTen fourthTen fineCount positiveCount direction
      moving paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage //
    value = completed.positiveTable firstTen secondTen thirdTen fourthTen fineCount positiveCount direction moving
      paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage }) ×
  (trace : EulerExecution.TraceCache (spatial := spatial) grid.val) ×
  { values : Vec Canonical 2 //
    EulerExecution.ValuesPredicate (request := request) (spatial := spatial) grid.val trace.val values }

/-- Compute the original finite schedule, acquire one literal grid and execute its original Euler trace once.

The supplied fine Completion is the existing genuine initial geometric
certificate. The original positiveTable factory derives the common source
and all node completions. No target Completion, good-refinement witness,
programme equality or desired final error is supplied. Node0 is the same
completed source; stationary and canonical attachments remain independent.
-/
def eulerExecution
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
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage :=
  let selection : Search.Selection
      (Euler.endpointScale (PositiveGridNode.coarseIntervals frame direction)
        (PositiveGridNode.taylorFactor requested.covered direction)) 0 request.tolerance :=
    Euler.endpointSelection (PositiveGridNode.coarseIntervals frame direction)
      (PositiveGridNode.taylorFactor requested.covered direction)
      (PositiveGridNode.taylorFactor_nonnegative requested.covered direction) request
  let refinement := 4 ^ selection.stage
  let fineCount := PositiveGridNode.coarseIntervals frame direction * refinement
  have positiveCount : 0 < fineCount :=
    PositiveGridNode.fineIntervals_positive frame direction refinement (Nat.pow_pos (by decide))
  let paidSpatial := PositiveGridNode.connectionRequest frame fineCount positiveCount spatial
  Data.Sigma.pair ⟨selection, rfl⟩
    (Data.Sigma.ofSubtypeFactoriesWithTail
      (α := PositiveTable completed firstTen secondTen thirdTen fourthTen fineCount positiveCount direction
        moving paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
      (β := fun grid => Table.Trace grid.table)
      (γ := fun _ trace =>
        let boundedIndex := fun index : Nat => (⟨min index fineCount,
          Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
        let coefficients := fun index => Jets.Connection.alongMatrix
          (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
        { values : Vec Canonical 2 //
          values = Euler.trace coefficients (fun _ => 1 / (fineCount : Rational))
            (trace.eulerValues 0) fineCount ∧
          Norm.vector (zipWith (fun first last => first - last)
            (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩) values) < request.tolerance })
      (fun _ => completed.positiveTable firstTen secondTen thirdTen fourthTen fineCount positiveCount direction moving
        paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
      (fun grid => Table.Trace.build grid.table)
      (fun grid trace =>
        let boundedIndex := fun index : Nat => (⟨min index fineCount,
          Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
        let coefficients := fun index => Jets.Connection.alongMatrix
          (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
        let values : Vec Canonical 2 :=
          Euler.trace coefficients (fun _ => 1 / (fineCount : Rational)) (trace.eulerValues 0) fineCount
        have accurate : Norm.vector (zipWith (fun first last => first - last)
            (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩) values) < request.tolerance :=
          Table.Trace.requestedEndpoint_lt request selection trace grid.queries grid.completions
        ⟨values, rfl, accurate⟩))

/-- The complete execution retains the original four-factory construction in its original order.

All arithmetic lets, original factories and the final equality-plus-accuracy
certificate are the same values as the literal original tuple packing.
-/
private theorem eulerExecution_factory
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
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    : eulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage =
  let selection : Search.Selection
      (Euler.endpointScale (PositiveGridNode.coarseIntervals frame direction)
        (PositiveGridNode.taylorFactor requested.covered direction)) 0 request.tolerance :=
    Euler.endpointSelection (PositiveGridNode.coarseIntervals frame direction)
      (PositiveGridNode.taylorFactor requested.covered direction)
      (PositiveGridNode.taylorFactor_nonnegative requested.covered direction) request
  let refinement := 4 ^ selection.stage
  let fineCount := PositiveGridNode.coarseIntervals frame direction * refinement
  have positiveCount : 0 < fineCount :=
    PositiveGridNode.fineIntervals_positive frame direction refinement (Nat.pow_pos (by decide))
  let paidSpatial := PositiveGridNode.connectionRequest frame fineCount positiveCount spatial
  let grid : PositiveTable completed firstTen secondTen thirdTen fourthTen fineCount positiveCount direction
      moving paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage :=
    completed.positiveTable firstTen secondTen thirdTen fourthTen fineCount positiveCount direction moving
      paidSpatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage
  let trace : Table.Trace grid.table := Table.Trace.build grid.table
  let boundedIndex := fun index : Nat => (⟨min index fineCount,
    Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
  let coefficients := fun index => Jets.Connection.alongMatrix
    (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
  let values : Vec Canonical 2 :=
    Euler.trace coefficients (fun _ => 1 / (fineCount : Rational)) (trace.eulerValues 0) fineCount
  have accurate : Norm.vector (zipWith (fun first last => first - last)
      (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩) values) < request.tolerance :=
    Table.Trace.requestedEndpoint_lt request selection trace grid.queries grid.completions
  ⟨⟨selection, rfl⟩, ⟨grid, rfl⟩, ⟨trace, rfl⟩, ⟨values, rfl, accurate⟩⟩ := rfl

section Readbacks

variable
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
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

namespace EulerExecution

/-- Read the SAME original endpoint Selection, retaining its actual quotient, finite fuel and selected stage. -/
@[expose, macro_inline] def selection : Search.Selection
    (Euler.endpointScale (PositiveGridNode.coarseIntervals frame direction)
      (PositiveGridNode.taylorFactor requested.covered direction)) 0 request.tolerance := retained.1.val

/-- The computed fine refinement is the literal natural fourth power of the SAME stored selected stage. -/
@[expose, macro_inline] def refinement : Nat := 4 ^ retained.selection.stage

/-- The actual fine count combines the original fixed coarse count with that same selected refinement. -/
@[expose, macro_inline] def fineCount : Nat := PositiveGridNode.coarseIntervals frame direction * retained.refinement

/-- The original actual positive fine count has its constructive positivity certificate. -/
theorem fineCount_positive : 0 < retained.fineCount :=
  PositiveGridNode.fineIntervals_positive frame direction retained.refinement (Nat.pow_pos (by decide))

/-- Read the SAME whole original fine grid, common source/member, node programmes and target completions. -/
@[expose, macro_inline] def grid : PositiveTable completed firstTen secondTen thirdTen fourthTen retained.fineCount
    retained.fineCount_positive direction moving
    (PositiveGridNode.connectionRequest frame retained.fineCount retained.fineCount_positive spatial)
    commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage := retained.2.1.val

/-- Read the SAME once-built six-channel sample and four-row certificate cache. -/
@[expose, macro_inline] def trace : Table.Trace retained.grid.table := retained.2.2.1.val

/-- Read the SAME independently executed original Euler endpoint vector. -/
@[expose] def values : Vec Canonical 2 := retained.2.2.2.val

end EulerExecution

end Readbacks

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
