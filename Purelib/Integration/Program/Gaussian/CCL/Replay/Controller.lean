module
import Purelib.Data.Gaussian.Norm.Comparison
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observe
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
import Purelib.Approximation.Gaussian.Process.Normalization.Data
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
public import Purelib.Approximation.Gaussian.Process.Recipe.Inverse
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.CCL.Encoding.Padding.Residual
public import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission
public import Purelib.Data.CCL.Transducer.Replay.Emission.Step
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Program

/-!
# Finite numerical controller and adaptive replay

The controller's inspectable query constructions supply the phase decisions
for both ordinary replay and expanded model reads. Returned states retain
only finite chart syntax, rational bounds, source indices and bit lists.
Residual inversion requests its second model only after the actual first
reading selects that branch. Explicit source failures stop that continuation.
-/

@[expose] public section

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Controller

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process.Recipe (Cursor)
open Purelib.CCL.Progressive
open Purelib.Computation.Query (Program Protocol)
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Transducer.Replay (Failure)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Construct the original cursor observation at the initial budget and its checked initial emission. -/
def initialStepProgram (control : IntegrationReplay.Control) (cursor : Cursor) :
    IntegrationReplay.QueryProgram (Except Failure Replay.Emission) :=
  (Cursor.observeProgram control cursor Emission.Initial.Budget.initialRadiusSq).map fun result =>
    result.map fun (next, ball) => Replay.Emission.Step.initialAfter control next ball

/-- Execute the original initial emission query construction. -/
def initialStep (control : IntegrationReplay.Control) (cursor : Cursor) :
    IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  (initialStepProgram control cursor).protocol

/-- Initial execution retains the same observed cursor, emission and complete model-query log. -/
theorem initialStep_run (control : IntegrationReplay.Control) (cursor : Cursor)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (initialStep control cursor).run oracle =
      ((Cursor.observe control cursor Emission.Initial.Budget.initialRadiusSq).map fun result =>
        result.map fun (next, ball) => Replay.Emission.Step.initialAfter control next ball).run oracle :=
  Program.map_execution _ _ oracle

/-- Construct the retained low cursor observation at the initial budget and continue its exact count. -/
def lowStepProgram (control : IntegrationReplay.Control) (count : Nat) (cursor : Cursor) :
    IntegrationReplay.QueryProgram (Except Failure Replay.Emission) :=
  (Cursor.observeProgram control cursor Emission.Initial.Budget.initialRadiusSq).map fun result =>
    result.bind fun (next, ball) => Replay.Emission.Step.lowAfter control count next ball

/-- Execute the retained low emission query construction at its original count. -/
def lowStep (control : IntegrationReplay.Control) (count : Nat) (cursor : Cursor) :
    IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  (lowStepProgram control count cursor).protocol

/-- Low execution retains the same observation, count-indexed emission and complete model-query log. -/
theorem lowStep_run (control : IntegrationReplay.Control) (count : Nat) (cursor : Cursor)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (lowStep control count cursor).run oracle =
      ((Cursor.observe control cursor Emission.Initial.Budget.initialRadiusSq).map fun result =>
        result.bind fun (next, ball) => Replay.Emission.Step.lowAfter control count next ball).run oracle :=
  Program.map_execution _ _ oracle

/-- Construct the original loop cursor observation at its retained domain target and checked emission. -/
def loopStepProgram (control : IntegrationReplay.Control) (kind : Mode.Basic.RegularKind) (count : Nat)
    (cursor : Cursor) (domain : Process.Normalization.Data.Domain) :
    IntegrationReplay.QueryProgram (Except Failure Replay.Emission) :=
  (Cursor.observeProgram control cursor domain.target).map fun result =>
    result.bind fun (next, ball) => Replay.Emission.Step.loopAfter control kind count next ball

/-- Execute the original loop emission query construction at its retained domain target. -/
def loopStep (control : IntegrationReplay.Control) (kind : Mode.Basic.RegularKind) (count : Nat)
    (cursor : Cursor) (domain : Process.Normalization.Data.Domain) :
    IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  (loopStepProgram control kind count cursor domain).protocol

/-- Loop execution retains the same target-indexed observation, checked emission and complete model-query log. -/
theorem loopStep_run (control : IntegrationReplay.Control) (kind : Mode.Basic.RegularKind) (count : Nat)
    (cursor : Cursor) (domain : Process.Normalization.Data.Domain) (oracle : Nat → IntegrationReplay.CachedModel) :
    (loopStep control kind count cursor domain).run oracle =
      ((Cursor.observe control cursor domain.target).map fun result =>
        result.bind fun (next, ball) => Replay.Emission.Step.loopAfter control kind count next ball).run oracle :=
  Program.map_execution _ _ oracle

/-- Construct the retained residual padding decision or its exact inverse-loop observation.

Padding emits one true bit and retains the updated count and upper bound.
The inverse branch uses the same observed center and radius for its lower
estimate, then queries only the original inverse cursor and domain.
-/
def residualAfterProgram (control : IntegrationReplay.Control) (count : Nat) (upper : Fraction.Rational)
    (cursor : Cursor) (ball : Enclosure.Ball.Data.BallData) :
    IntegrationReplay.QueryProgram (Except Failure Replay.Emission) :=
  if Enclosure.Ball.Data.Bounds.smallUpper ball < Padding.Residual.paddingTarget (count + 1) then
    .pure (.ok ⟨[true], .residual cursor (count + 1) (Enclosure.Ball.Data.Bounds.smallUpper ball)⟩)
  else
    let lowerSq := Basic.Canonical.Norm.Comparison.normSqFromReduced ball.center / 2 - ball.radiusSq
    loopStepProgram control .loop count (Process.Recipe.Inverse.inverseCursor control cursor lowerSq count)
      (Process.Normalization.Data.inverseDomain count upper)

/-- Execute the retained residual padding or inverse-loop construction. -/
def residualAfter (control : IntegrationReplay.Control) (count : Nat) (upper : Fraction.Rational)
    (cursor : Cursor) (ball : Enclosure.Ball.Data.BallData) :
    IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  (residualAfterProgram control count upper cursor ball).protocol

/-- Residual execution keeps the same padding decision and conditional inverse-loop query log. -/
theorem residualAfter_run (control : IntegrationReplay.Control) (count : Nat) (upper : Fraction.Rational)
    (cursor : Cursor) (ball : Enclosure.Ball.Data.BallData) (oracle : Nat → IntegrationReplay.CachedModel) :
    (residualAfter control count upper cursor ball).run oracle =
      (if Enclosure.Ball.Data.Bounds.smallUpper ball < Padding.Residual.paddingTarget (count + 1) then
        .pure (.ok ⟨[true], .residual cursor (count + 1) (Enclosure.Ball.Data.Bounds.smallUpper ball)⟩)
      else
        let lowerSq := Basic.Canonical.Norm.Comparison.normSqFromReduced ball.center / 2 - ball.radiusSq
        loopStep control .loop count (Process.Recipe.Inverse.inverseCursor control cursor lowerSq count)
          (Process.Normalization.Data.inverseDomain count upper)).run oracle := by
  unfold residualAfter residualAfterProgram
  split <;> rfl

/-- Construct the retained residual observation, preserving its failure before any inverse-loop request. -/
def residualStepProgram (control : IntegrationReplay.Control) (cursor : Cursor) (count : Nat)
    (upper : Fraction.Rational) : IntegrationReplay.QueryProgram (Except Failure Replay.Emission) :=
  (Cursor.observeProgram control cursor (Padding.Residual.paddingTarget (count + 1) / 6)).bind fun result =>
    match result with
    | .error error => .pure (.error error)
    | .ok (next, ball) => residualAfterProgram control count upper next ball

/-- Execute the retained residual observation and its actual selected continuation. -/
def residualStep (control : IntegrationReplay.Control) (cursor : Cursor) (count : Nat)
    (upper : Fraction.Rational) : IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  (residualStepProgram control cursor count upper).protocol

/-- Residual execution stops at the same source failure or consumes its original successful observation once. -/
theorem residualStep_run (control : IntegrationReplay.Control) (cursor : Cursor) (count : Nat)
    (upper : Fraction.Rational) (oracle : Nat → IntegrationReplay.CachedModel) :
    (residualStep control cursor count upper).run oracle =
      ((Cursor.observe control cursor (Padding.Residual.paddingTarget (count + 1) / 6)).bind fun result =>
        match result with
        | .error error => .pure (.error error)
        | .ok (next, ball) => residualAfter control count upper next ball).run oracle := by
  rewrite [residualStep, residualStepProgram, Program.bind_execution]
  apply Protocol.bind_execution_eq _ _ _ _ oracle rfl
  cases ((Cursor.observeProgram control cursor (Padding.Residual.paddingTarget (count + 1) / 6)).protocol.run
    oracle).value with
  | error error => rfl
  | ok value => cases value; rfl

/-- Construct one replay-controller step from its exact retained mode, cursor, count and domain. -/
def stepProgram (control : IntegrationReplay.Control) :
    Replay.Mode → IntegrationReplay.QueryProgram (Except Failure Replay.Emission)
  | .initial cursor => initialStepProgram control cursor
  | .low count cursor => lowStepProgram control count cursor
  | .loop kind count cursor domain => loopStepProgram control kind count cursor domain
  | .residual cursor count upper => residualStepProgram control cursor count upper

/-- Execute the exact retained mode's shared controller construction. -/
def step (control : IntegrationReplay.Control) :
    Replay.Mode → IntegrationReplay.QueryComputation (Except Failure Replay.Emission) :=
  fun mode => (stepProgram control mode).protocol

end Purelib.Integration.Program.Gaussian.CCL.Replay.Controller
