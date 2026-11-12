module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Reference.Comparison
import Purelib.Integration.Program.Comparison
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Operational agreement with one retained endpoint programme

One original finite execution is stored at accuracy index zero. Its same
endpoint programme is retained once, and the geometric Euler stream keeps
that execution at index zero. Original programme comparisons derive the
named output relation without duplicating the reference execution, using
an approximate target-model replacement or accepting desired closeness.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data
open Purelib.Curves.Legendre.Periods.Jets.Specification
namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Approximation.Rational
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration
open Steps.Acquisition

section

variable
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {circuitExecution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) circuitExecution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- One original cached reference, its original target programme, the Euler programme and their actual named relation.

Existing dependent tuples/subtypes retain complete factory identities.
The source Completion, reference Request, target programme preparation
family and all six original row caches stay inside the same execution.
-/
@[expose] def EndpointProgrammeComparison (coordinate : Fin 2) :=
  (reference : EulerExecution.Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial
    commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage) ×
  (target : reference.Target coordinate) ×
  (computed : reference.Computed coordinate) ×
  NamedEquivalent computed.val.output.name target.val.output.name

namespace EndpointProgrammeComparison

variable {completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges allocation
    admitted widths targetCurrent targetFloor targetRootStage}

/-- Retain both original programmes and their derived comparison on this same reference execution.

The reference is supplied as a retained value. Its target programme and
computed programme are each materialized once before the original
comparison constructor consumes those same two cached values.
-/
@[noinline] def ofReference
    (reference : EulerExecution.Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    (coordinate : Fin 2) :
    EndpointProgrammeComparison completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage coordinate :=
  let target : reference.Target coordinate :=
    ⟨reference.val.endpointProgrammes.targetProgram (next := reference.val.endpointShifted)
      (Table.valueIndex coordinate), rfl⟩
  let computed : reference.Computed coordinate := ⟨reference.programme coordinate, rfl⟩
  let compared := reference.equivalent coordinate target computed
  ⟨reference, target, computed, compared⟩

end EndpointProgrammeComparison

/-- Execute one reference endpoint once and retain both whole programmes before constructing their derived comparison.

The geometric stream consumes that same reference at index zero and in
its center. The original target programme is materialized once from the
same retained endpoint blocks. Comparison requests may invoke genuine
positive-index finite executions; no historical memoization is claimed.
-/
@[expose, macro_inline] def eulerProgrammeComparison (coordinate : Fin 2) :
    EndpointProgrammeComparison completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage coordinate :=
  let reference : EulerExecution.Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage :=
    ⟨executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage 0, rfl⟩
  EndpointProgrammeComparison.ofReference reference coordinate

namespace EndpointProgrammeComparison

variable {completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges allocation
    admitted widths targetCurrent targetFloor targetRootStage} {coordinate : Fin 2}
    (retained : EndpointProgrammeComparison completed firstTen secondTen thirdTen fourthTen direction moving spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage coordinate)

/-- Read the same original reference execution and its complete accuracy-zero factory equation. -/
@[expose, macro_inline]
def reference : EulerExecution.Reference completed firstTen secondTen thirdTen fourthTen direction moving
    spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage := retained.1

/-- Read the SAME original target RefinementProgram, without reconstructing any model or preparation. -/
@[expose, macro_inline] def target : RefinementProgram := retained.2.1.val

/-- Read the stored original exact-Euler-sample RefinementProgram. -/
@[expose, macro_inline] def computed : RefinementProgram := retained.2.2.1.val

/-- Read the derived original operational comparison on these two SAME stored programme values. -/
@[expose, macro_inline]
def comparison : NamedEquivalent retained.computed.output.name retained.target.output.name := retained.2.2.2

/-- The whole stored target programme is its original reference endpoint factory on the same retained row cache. -/
theorem target_eq : retained.target = retained.reference.val.endpointProgrammes.targetProgram
    (next := retained.reference.val.endpointShifted) (Table.valueIndex coordinate) :=
  retained.2.1.property

/-- The target programme remains the whole literal original untransported endpoint programme as well. -/
theorem target_original : retained.target =
    (retained.reference.val.grid.table.programmes.entry retained.reference.val.endpointIndex).targetProgram
      (next := (retained.reference.val.grid.table.nodes.node retained.reference.val.endpointIndex).next)
      (Table.valueIndex coordinate) :=
  retained.target_eq.trans (retained.reference.val.endpointProgrammes_program
    (Table.valueIndex coordinate))

/-- The stored Euler programme is the exact original generic programme factory on this SAME cached reference. -/
theorem computed_eq : retained.computed = retained.reference.programme coordinate := retained.2.2.1.property

/-- Every computed model reads its same actual finite Euler execution, including the cached zero branch. -/
theorem computed_sample (index : Nat) : (retained.computed.model index).integralSample =
    (retained.reference.execution index).values coordinate :=
  (congrArg (fun value : RefinementProgram => (value.model index).integralSample) retained.computed_eq).trans
    ((retained.reference.programme_sample coordinate index).trans
      (retained.reference.sample_execution coordinate index))

end EndpointProgrammeComparison

end

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
