module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Increment
import Purelib.Data.Vector.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Rational.Grid.Unit

import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Original geometric endpoint and programme views of one retained Euler execution -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Periods.Jets.Specification

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Rational
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
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

/-- Select the literal last positive node from the same constructed positive grid, including a one-edge grid. -/
@[expose] def endpointIndex : Fin retained.fineCount :=
  ⟨retained.fineCount - 1, Nat.sub_lt retained.fineCount_positive (by decide : 0 < 1)⟩

/-- That last node's successor is the exact retained terminal sample position. -/
theorem endpointIndex_succ : retained.endpointIndex.succ =
    (⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩ : Fin (retained.fineCount + 1)) :=
  Fin.ext (Nat.sub_add_cancel (Nat.succ_le_of_lt retained.fineCount_positive))

/-- The same final positive node has the original whole requested Gaussian direction as its absolute offset.

This scalar identity changes no frame, Request, polynomial or source owner.
The actual node still retains its original targetFrame factory and caches.
-/
theorem endpoint_offset_eq : Sampling.gridOffset retained.fineCount retained.endpointIndex.succ direction =
    direction := by
  have last : retained.endpointIndex.succ.val = retained.fineCount :=
    congrArg Fin.val retained.endpointIndex_succ
  have endpoint := Grid.Unit.node_one retained.fineCount_positive retained.endpointIndex.succ last
  have scaled : Scale.scale 1 direction = direction := by
    apply Data.Gaussian.Basic.ext
    · exact (Scale.scale_re 1 direction).trans (Fraction.Field.one_mul direction.re)
    · exact (Scale.scale_im 1 direction).trans (Fraction.Field.one_mul direction.im)
  exact (congrArg (fun width => Scale.scale width direction) endpoint).trans scaled

/-- The actual terminal frame is the same whole original fixed-endpoint frame after exact parameter transport.

The retained node target factory and literal final grid-offset equality
supply the complete frame identity. Equal coordinates or branch labels
alone are not used to identify frame data.
-/
theorem endpoint_frame_eq :
    (retained.grid.table.nodes.node retained.endpointIndex).target.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) retained.endpoint_offset_eq) =
      ranges.targetFrame direction (admitted.trans allocation.bound_le_regularBound) := by
  have actual := congrArg
    (fun original : Paths.Frame
      (parameter + Sampling.gridOffset retained.fineCount retained.endpointIndex.succ direction) =>
        original.castParameter
          (congrArg (fun increment : Canonical => parameter + increment) retained.endpoint_offset_eq))
    (retained.grid.table.nodes.node retained.endpointIndex).target_eq
  exact actual.trans (ranges.targetFrame_castParameter
    (((Sampling.gridOffset_normSq_le retained.fineCount retained.fineCount_positive
      retained.endpointIndex.succ direction).trans admitted).trans allocation.bound_le_regularBound)
    (admitted.trans allocation.bound_le_regularBound) retained.endpoint_offset_eq)

/-- Read the same whole terminal shifted cache at the original fixed direction and complete endpoint frame.

The original source accuracy is transported by its exact increment
identity. No source selection, block, geometry, target Request or checking
factory is executed by this view.
-/
@[expose, macro_inline] def endpointShifted :
    PreparedParents.StageAttempt.Requested.Shifted.AtIncrement
      (lastIncrement := direction) (lastTarget := ranges.targetFrame direction
        (admitted.trans allocation.bound_le_regularBound))
      (lastNonzero := moving) (lastAdmitted := admitted)
      (retained.grid.table.nodes.node retained.endpointIndex).next retained.endpoint_offset_eq :=
  PreparedParents.StageAttempt.Requested.Shifted.castIncrement
    (lastNonzero := moving) (lastAdmitted := admitted)
    (retained.grid.table.nodes.node retained.endpointIndex).next
    retained.endpoint_offset_eq retained.endpoint_frame_eq

/-- The terminal view retains the entire original shifted tuple and all its whole factory equations. -/
theorem endpointShifted_heq :
    HEq retained.endpointShifted (retained.grid.table.nodes.node retained.endpointIndex).next :=
  PreparedParents.StageAttempt.Requested.Shifted.castIncrement_heq
    (lastNonzero := moving) (lastAdmitted := admitted)
    (retained.grid.table.nodes.node retained.endpointIndex).next
    retained.endpoint_offset_eq retained.endpoint_frame_eq

/-- Read the same whole terminal four-row cache at its fixed endpoint view, without building any new row.

The original positions, Alignments, restriction banks, Sample families and
integral certificates are equality-transported together with their Request.
-/
@[expose, macro_inline] def endpointProgrammes :
    PreparedParents.ShiftedGeometry.ValueBlocks.AtIncrement
      (lastIncrement := direction) (lastTarget := ranges.targetFrame direction
        (admitted.trans allocation.bound_le_regularBound))
      (lastNonzero := moving) (lastAdmitted := admitted)
      (retained.grid.table.programmes.entry retained.endpointIndex)
      retained.endpoint_offset_eq retained.endpoint_frame_eq :=
  PreparedParents.ShiftedGeometry.ValueBlocks.castIncrement
    (lastNonzero := moving) (lastAdmitted := admitted)
    (retained.grid.table.programmes.entry retained.endpointIndex)
    retained.endpoint_offset_eq retained.endpoint_frame_eq

/-- All six whole original terminal programmes survive the fixed-endpoint cache transport.

Every stage, model allowance, original sample, tail comparison and center
bound remains part of the same programme; no approximate sample is used
as an exact model replacement.
-/
theorem endpointProgrammes_program (channel : Fin 6) :
    retained.endpointProgrammes.targetProgram (next := retained.endpointShifted) channel =
      (retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
        (next := (retained.grid.table.nodes.node retained.endpointIndex).next) channel :=
  PreparedParents.ShiftedGeometry.ValueBlocks.castIncrement_targetProgram
    (lastNonzero := moving) (lastAdmitted := admitted)
    (retained.grid.table.programmes.entry retained.endpointIndex)
    retained.endpoint_offset_eq retained.endpoint_frame_eq channel

/-- The literal terminal grid value is the SAME last stored target programme's selected-stage reading. -/
theorem terminal_sample (coordinate : Fin 2) :
    retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩ coordinate =
      (((retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
        (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
        (Table.valueIndex coordinate)).model
          (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage).integralSample :=
  (vectorOfFn_apply (fun coordinate => retained.trace.sample
    ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩
    (Table.valueIndex coordinate)) coordinate).trans
      ((retained.trace.sample_eq ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩
        (Table.valueIndex coordinate)).trans
          ((congrArg (fun position => retained.grid.table.sampleAt position
            (Table.valueIndex coordinate)) retained.endpointIndex_succ.symm).trans
              (retained.grid.table.sampleAt_succ retained.endpointIndex
                (Table.valueIndex coordinate))))

end EulerExecution

end

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
