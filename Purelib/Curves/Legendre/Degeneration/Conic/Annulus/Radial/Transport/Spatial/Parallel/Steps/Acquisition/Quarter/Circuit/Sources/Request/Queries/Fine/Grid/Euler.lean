module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Execution
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Schedule
import Purelib.Data.Vector.Basic

/-! # Exact factory and endpoint readbacks of the retained finite Euler execution -/

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

/-- The whole retained Selection is the original search factory on the same fixed geometry and requested tolerance. -/
theorem selection_eq : retained.selection =
    Euler.endpointSelection (PositiveGridNode.coarseIntervals frame direction)
      (PositiveGridNode.taylorFactor requested.covered direction)
      (PositiveGridNode.taylorFactor_nonnegative requested.covered direction) request := retained.1.property

/-- The whole retained grid is the original single positiveTable factory at its actually paid request. -/
theorem grid_eq : retained.grid = completed.positiveTable firstTen secondTen thirdTen fourthTen retained.fineCount
    retained.fineCount_positive direction moving
    (PositiveGridNode.connectionRequest frame retained.fineCount retained.fineCount_positive spatial)
    commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage := retained.2.1.property

/-- The whole original trace cache is its once-executed factory on the SAME original table. -/
theorem trace_eq : retained.trace = Table.Trace.build retained.grid.table := retained.2.2.1.property

/-- The original Euler vector keeps the complete factory equality with the same retained sample/matrix sequence. -/
theorem values_eq :
    let boundedIndex := fun index : Nat => (⟨min index retained.fineCount,
      Nat.lt_succ_of_le (Nat.min_le_right index retained.fineCount)⟩ : Fin (retained.fineCount + 1))
    retained.values = Euler.trace
      (fun index => Jets.Connection.alongMatrix
        (parameter + Sampling.gridOffset retained.fineCount (boundedIndex index) direction) direction)
      (fun _ => 1 / (retained.fineCount : Rational)) (retained.trace.eulerValues 0) retained.fineCount :=
  retained.2.2.2.property.1

/-- The same original terminal programme samples meet the requested quadrance against the computed Euler vector. -/
theorem endpoint_lt :
    Norm.vector (zipWith (fun first last => first - last)
      (retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩) retained.values) <
        request.tolerance := retained.2.2.2.property.2

/-- The actual initial executor vector reads the SAME retained common source's two original value channels. -/
theorem initial_values : retained.trace.eulerValues 0 =
    Data.Vector.Basic.vectorOfFn (fun coordinate =>
      PositiveGridNode.sourceSample retained.grid.common.1 retained.grid.common.2
        (Jets.Specification.Table.valueIndex coordinate)) := retained.trace.eulerValues_zero

end EulerExecution

end Readbacks

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
