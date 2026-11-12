module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Relations
public import Purelib.Integration.Program.Comparison
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Progressive Euler endpoints on one retained fixed physical window

Every finite sample executes the original requested Euler constructor at
its quarter-radius tolerance. Both endpoint programme owners are compared
through the original fixed-source-geometry refinement theorem. No desired
sample bound, all-stage agreement or replacement target model is supplied.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib.Data
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
open Steps.Acquisition

/-- The closed unit rational is positive. -/
private theorem onePositive : (0 : Rational) < 1 := by decide +kernel
/-- The closed multiplier two is nonnegative. -/
private theorem twoNonnegative : (0 : Rational) ≤ 2 := by decide +kernel
/-- The closed multiplier four is nonnegative. -/
private theorem fourNonnegative : (0 : Rational) ≤ 4 := by decide +kernel
/-- The closed constant six is nonnegative. -/
private theorem sixNonnegative : (0 : Rational) ≤ 6 := by decide +kernel

/-- The two endpoint budgets and middle programme budget have combined scale six plus four times scale. -/
private theorem weighted_radius (scale : Rational) (index : Nat) :
    2 * (Geometric.Basic.quarterRadius 1 index +
      2 * (Geometric.Basic.quarterRadius scale index + Geometric.Basic.quarterRadius 1 index)) =
      Geometric.Basic.quarterRadius (6 + 4 * scale) index :=
  (Geometric.Basic.quarterRadius_weighted_sum 1 scale 1 index).trans
    (congrArg (fun value : Rational => Geometric.Basic.quarterRadius value index) (by ring1))

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
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

section EndpointReadbacks

variable {completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

namespace EulerExecution

/-- Read the original last-node target selection stage without reindexing the request. -/
@[expose, macro_inline] def endpointStage : Nat :=
  (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage

/-- Read the literal retained endpoint programme at its original selected stage. -/
@[expose, macro_inline] def endpointSample (coordinate : Fin 2) : Canonical :=
  (((retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (Jets.Specification.Table.valueIndex coordinate)).model retained.endpointStage).integralSample

/-- The retained endpoint programme reads the same terminal vector used by the execution payment. -/
theorem endpointSample_eq (coordinate : Fin 2) : retained.endpointSample coordinate =
    retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩ coordinate :=
  (retained.terminal_sample coordinate).symm

/-- Whole-programme transport preserves the same original endpoint sample at its original stage. -/
theorem endpointSample_fixed (coordinate : Fin 2) : retained.endpointSample coordinate =
    ((retained.endpointProgrammes.targetProgram (next := retained.endpointShifted)
      (Jets.Specification.Table.valueIndex coordinate)).model retained.endpointStage).integralSample :=
  (congrArg (fun original : RefinementProgram =>
    (original.model retained.endpointStage).integralSample)
      (retained.endpointProgrammes_program (Jets.Specification.Table.valueIndex coordinate))).symm

/-- The original endpoint selection pays the requested target-stage floor. -/
theorem endpoint_stage_ge : targetCurrent ≤ retained.endpointStage :=
  (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.lower

/-- Each actual coordinate is paid by the original whole-vector endpoint inequality. -/
theorem endpoint_coordinate_lt (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.endpointSample coordinate - retained.values coordinate) < request.tolerance := by
  let difference := Data.Vector.zipWith (fun first last : Canonical => first - last)
    (retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩) retained.values
  have displayed := Data.Vector.Basic.zipWith_apply (fun first last : Canonical => first - last)
    (retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩)
    retained.values coordinate
  have sample := congrArg (fun value : Canonical => value - retained.values coordinate)
    (retained.endpointSample_eq coordinate)
  exact ((congrArg Norm.Basic.normSq (sample.trans displayed.symm)).trans_le
    (LinearAlgebra.Gaussian.Norm.coordinate_le_vector difference coordinate)).trans_lt retained.endpoint_lt

/-- Two owned finite executions compare through their distinct actual target programmes on the same fixed window.

The endpoint payments are original retained certificates. The middle
comparison is constructed from the two actual preparation families and
common restrictions by targetPrograms_later_close, at their own selected
stages. Only the elementary lower bounds on requested stage starts enter.
-/
theorem endpoint_pair_le
    {lastRequest : AccuracyRequest} {lastTargetCurrent : Nat}
    (last : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving lastRequest spatial
      commonCurrent ranges allocation admitted widths lastTargetCurrent targetFloor targetRootStage)
    (coordinate : Fin 2) (earlier : Nat)
    (firstAfter : earlier ≤ targetCurrent) (lastAfter : earlier ≤ lastTargetCurrent) :
    Norm.Basic.normSq (retained.values coordinate - last.values coordinate) ≤
      2 * (request.tolerance + 2 * (Geometric.Basic.quarterRadius
        (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) earlier +
          lastRequest.tolerance)) := by
  have firstPaid := (Norm.Bounds.normSq_sub_symm
    (retained.values coordinate) (retained.endpointSample coordinate)).trans_le
      (le_of_lt (retained.endpoint_coordinate_lt coordinate))
  have middle := PreparedParents.ShiftedGeometry.ValueBlocks.targetPrograms_later_close
    (firstNext := retained.endpointShifted) (lastNext := last.endpointShifted)
    retained.endpointProgrammes last.endpointProgrammes (Jets.Specification.Table.valueIndex coordinate)
    earlier retained.endpointStage last.endpointStage
    (firstAfter.trans retained.endpoint_stage_ge) (lastAfter.trans last.endpoint_stage_ge)
  have middleActual := (congrArg Norm.Basic.normSq
    (congrArg₂ (fun first last : Canonical => first - last)
      (retained.endpointSample_fixed coordinate) (last.endpointSample_fixed coordinate))).trans_le middle
  exact Norm.Bounds.normSq_sub_le_weighted_sum
    (retained.values coordinate) (retained.endpointSample coordinate)
    (last.endpointSample coordinate) (last.values coordinate)
    request.tolerance
    (Geometric.Basic.quarterRadius
      (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) earlier)
    lastRequest.tolerance firstPaid middleActual (le_of_lt (last.endpoint_coordinate_lt coordinate))

end EulerExecution

end EndpointReadbacks

variable {request}

/-- The actual request for the finite Euler execution at a stream index. -/
@[expose] def streamRequest (index : Nat) : AccuracyRequest :=
  ⟨Geometric.Basic.quarterRadius 1 index,
    Geometric.Basic.quarterRadius_pos (Cast.Order.natCast_pos_direct (n := 1) (by decide)) index⟩

/-- The exact original finite execution family, with target starts above the corresponding stream index. -/
@[expose] def ExecutionAt (index : Nat) : Type _ :=
  EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving (streamRequest index) spatial
    commonCurrent ranges allocation admitted widths (max targetCurrent index) targetFloor targetRootStage

/-- Run the original requested finite constructor once for this invocation and this retained source window.

The index changes the requested endpoint tolerance and sufficient target
start. No infinite cache or historical memoization is asserted. Each finite
result retains its own original Selection, grid, programmes and completions.
-/
def executionAt (index : Nat) : ExecutionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial
    commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage index :=
  completed.eulerExecution firstTen secondTen thirdTen fourthTen direction moving (streamRequest index) spatial
    commonCurrent ranges allocation admitted widths (max targetCurrent index) targetFloor targetRootStage

/-- The complete finite execution is its original constructor at the computed tolerance and sufficient stage floor. -/
theorem executionAt_eq (index : Nat) :
    executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index =
    completed.eulerExecution firstTen secondTen thirdTen fourthTen direction moving (streamRequest index) spatial
      commonCurrent ranges allocation admitted widths (max targetCurrent index) targetFloor targetRootStage := by rfl

/-- The computed movement scale uses both owned endpoint errors and the original fixed-geometry programme scale. -/
@[expose] def streamScale : Rational :=
  6 + 4 * PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)

/-- The same movement scale is nonnegative even when every original physical displacement is zero. -/
theorem streamScale_nonnegative : (0 : Rational) ≤ streamScale (requested := requested) := by
  have nonnegative := Order.Arithmetic.add_le_add_direct sixNonnegative
    (Order.Arithmetic.mul_nonneg_direct fourNonnegative
      (PreparedParents.errorScale_nonnegative (requested.shape.val.1 :: requested.shape.val.2)))
  exact (Data.Rat.Fraction.Field.zero_add 0).symm.trans_le nonnegative

/-- Every two actual later executions satisfy the exact quarter-radius movement estimate 6 + 4E. -/
theorem executionAt_later_close (coordinate : Fin 2) {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq
      ((executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
        allocation admitted widths targetCurrent targetFloor targetRootStage later).values coordinate -
       (executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
        allocation admitted widths targetCurrent targetFloor targetRootStage earlier).values coordinate) ≤
      Geometric.Basic.quarterRadius (streamScale (requested := requested)) earlier := by
  let first := executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage later
  let last := executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage earlier
  have actual := first.endpoint_pair_le last coordinate earlier
    (order.trans (Nat.Order.le_max_right targetCurrent later)) (Nat.Order.le_max_right targetCurrent earlier)
  have firstPaid := Geometric.Basic.quarterRadius_antitone (le_of_lt onePositive) order
  have totalPaid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct firstPaid
      (show (2 : Rational) * (Geometric.Basic.quarterRadius
          (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) earlier +
          Geometric.Basic.quarterRadius 1 earlier) ≤ _ from le_refl _)) twoNonnegative
  exact (actual.trans totalPaid).trans_eq
    (weighted_radius (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) earlier)

/-- Keep the original index-zero execution in the sample closure rather than executing it again at index zero. -/
@[expose] def streamSample
    (reference : ExecutionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage 0)
    (coordinate : Fin 2) : Nat → Canonical
  | 0 => reference.values coordinate
  | index + 1 => (executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage (index + 1)).values coordinate

namespace EulerExecution

/-- Retain one whole original finite reference execution with its complete factory identity.

The zero here is an accuracy-stream index. Its actual physical endpoint is
still the same admitted nonzero direction, not a zero parameter offset.
-/
@[expose] def Reference :=
  { value : ExecutionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage 0 //
    value = executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage 0 }

namespace Reference

variable {completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges allocation
    admitted widths targetCurrent targetFloor targetRootStage}
    (reference : Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

/-- Read the retained reference at zero and construct each original positive-index execution only on invocation. -/
@[expose, macro_inline] def execution : (index : Nat) →
    ExecutionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index
  | 0 => reference.val
  | index + 1 => executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage (index + 1)

/-- Every selected execution has the whole original factory value; the zero case uses its already stored proof. -/
theorem execution_eq (index : Nat) : reference.execution index =
    executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index := by
  cases index with
  | zero => exact reference.property
  | succ index => rfl

/-- The original streamSample operation keeps this SAME reference value in its zero branch. -/
@[expose] def sample (coordinate : Fin 2) (index : Nat) : Canonical :=
  streamSample completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
    allocation admitted widths targetCurrent targetFloor targetRootStage reference.val coordinate index

/-- The scalar stream reads precisely the corresponding original retained execution vector. -/
theorem sample_execution (coordinate : Fin 2) (index : Nat) :
    reference.sample coordinate index = (reference.execution index).values coordinate := by
  cases index <;> rfl

/-- The scalar readback uses the whole original factory equality without executing a reference a second time. -/
theorem sample_eq (coordinate : Fin 2) (index : Nat) : reference.sample coordinate index =
    (executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index).values coordinate :=
  (reference.sample_execution coordinate index).trans
    (congrArg (fun value : ExecutionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage index =>
        value.values coordinate) (reference.execution_eq index))

/-- The same stored reference supplies a productive Euler approximation with internally derived movement and center.

Only existing streamSample/executionAt and original endpoint payments are
used. This constructor does not call executionAt at zero: it consumes the
retained reference. Positive finite invocations remain genuine new work.
-/
def approximation (coordinate : Fin 2) : GeometricApproximation := by
  have movement {earlier later : Nat} (order : earlier ≤ later) :
      Norm.Basic.normSq (reference.sample coordinate later - reference.sample coordinate earlier) ≤
        Geometric.Basic.quarterRadius (streamScale (requested := requested)) earlier :=
    (congrArg Norm.Basic.normSq (congrArg₂ (fun first last : Canonical => first - last)
      (reference.sample_eq coordinate later) (reference.sample_eq coordinate earlier))).trans_le
        (executionAt_later_close completed firstTen secondTen thirdTen fourthTen direction moving spatial
          commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage coordinate order)
  let center := 2 * (streamScale (requested := requested) + Norm.Basic.normSq (reference.val.values coordinate))
  have centerNonnegative : (0 : Rational) ≤ center := by
    have terms := Order.Arithmetic.add_le_add_direct (streamScale_nonnegative (requested := requested))
      (Norm.Basic.normSq_nonneg (reference.val.values coordinate))
    exact Order.Arithmetic.mul_nonneg_direct twoNonnegative
      ((Field.zero_add 0).symm.trans_le terms)
  have bounded (index : Nat) : Norm.Basic.normSq (reference.sample coordinate index) ≤ center := by
    have difference := (movement (Nat.zero_le index)).trans
      (Geometric.Basic.quarterRadius_le_scale (streamScale_nonnegative (requested := requested)) 0)
    have decomposition : reference.sample coordinate index =
        (reference.sample coordinate index - reference.sample coordinate 0) + reference.sample coordinate 0 := by
      ring1
    have triangle := (congrArg Norm.Basic.normSq decomposition).trans_le
      (Norm.Bounds.normSq_add_le_two
        (reference.sample coordinate index - reference.sample coordinate 0) (reference.sample coordinate 0))
    exact triangle.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct difference
        (le_refl (Norm.Basic.normSq (reference.sample coordinate 0)))) twoNonnegative)
  exact ⟨reference.sample coordinate, streamScale (requested := requested),
    streamScale_nonnegative (requested := requested), @movement, center, centerNonnegative, bounded⟩

/-- The productive owner keeps the actual Euler sample without any target-model substitution. -/
theorem approximation_sample (coordinate : Fin 2) (index : Nat) :
    (reference.approximation coordinate).sample index = reference.sample coordinate index := by rfl

end Reference

end EulerExecution

/-- Build the existing productive geometric owner from actual finite Euler vectors and internally proved bounds.

One actual reference execution supplies the center. Every later sample
uses its original execution at the displayed index. The center and later
bound are derived here; no desired coherence or target relation is input.
-/
@[expose, macro_inline] def eulerApproximation (coordinate : Fin 2) : GeometricApproximation :=
  let reference : EulerExecution.Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage :=
    ⟨executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage 0, rfl⟩
  reference.approximation coordinate

/-- The productive Euler owner reads the literal original finite executor vector at every index. -/
theorem eulerApproximation_sample (coordinate : Fin 2) (index : Nat) :
    (eulerApproximation completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage coordinate).sample index =
    (executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index).values coordinate := by
  cases index <;> rfl

/-- Represent the Euler stream by the existing exact-sample refinement programme, leaving all target owners intact. -/
def eulerProgram (coordinate : Fin 2) : RefinementProgram :=
  Integration.Program.Comparison.geometricRefinementProgram
    (eulerApproximation completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage coordinate)

/-- Each programme model carries the exact computed Euler coordinate while preserving the original target model. -/
theorem eulerProgram_sample (coordinate : Fin 2) (index : Nat) :
    ((eulerProgram completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage coordinate).model index).integralSample =
    (executionAt completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges
      allocation admitted widths targetCurrent targetFloor targetRootStage index).values coordinate :=
  (Integration.Program.Comparison.geometricRefinementProgram_integralSample _ index).trans
    (eulerApproximation_sample completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage coordinate index)

end

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
