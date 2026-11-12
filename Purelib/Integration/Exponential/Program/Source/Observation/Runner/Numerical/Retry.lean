module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical
public import Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Resume

/-!
# Resume the actual interrupted production and numerical comparison

The original production, numerical state, effective banks and stopped common
batch remain fixed. A retry resumes the retained Gaussian ball and only the
original untouched common suffix.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Retry

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Program.Source.Observation.Numerical
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.SourceFrontier
open Purelib.Integration.NumericalFrontier.Common.Observation

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Numerical.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

/-- The finite Taylor source selected by the actual returned production receipt. -/
abbrev depth (production : Full.Result input.production) := production.comparison.receipt.selection.depth

/-- The actual original selected finite frontier. -/
abbrev left (production : Full.Result input.production) := Numerical.exactFrontier input production

/-- The original effective finite point bank used by the interrupted batch. -/
abbrev effectiveLeft (production : Full.Result input.production) :=
  Independent.Cache.leftAvailable (left input production) (Numerical.selectedBank input production)

/-- The original effective numerical point bank used by the interrupted batch. -/
abbrev effectiveRight (numerical : Numerical.NumericalDone input) :=
  Independent.Cache.rightAvailable numerical.state.1 input.rightBank

/-- A stopped common batch retaining its actual effective banks and current saved tails. -/
abbrev Stopped (production : Full.Result input.production) (numerical : Numerical.NumericalDone input)
    (savedLeft : List (NumericalPoint (Points.finiteProcess (depth input production))))
    (savedRight : List (NumericalPoint Horner.Real.source)) :=
  Points.Resume.Stopped (depth input production) (left input production) numerical.state.1
    (effectiveLeft input production) (effectiveRight input numerical) input.pointRequest savedLeft savedRight

set_option genInjectivity false in
/-- The actual original mixed failure and its currently stopped common-batch continuation. -/
structure Request where
  /-- The actual returned production owner. -/ production : Full.Result input.production
  /-- The actual returned numerical history owner. -/ numerical : Numerical.NumericalDone input
  /-- The original common execution returned by that mixed attempt. -/ execution :
    Numerical.CommonExecution input production numerical
  /-- Its exact first stopped batch. -/ original : Numerical.CommonFailure input production numerical
  /-- The original execution returned the retained stopped batch. -/ returned : execution.value = .error original
  /-- The currently saved finite-source points. -/ savedLeft :
    List (NumericalPoint (Points.finiteProcess (depth input production)))
  /-- The currently saved independent numerical points. -/ savedRight : List (NumericalPoint Horner.Real.source)
  /-- The current original-order stopped batch, with its exact certified prefix. -/ stopped :
    Stopped input production numerical savedLeft savedRight

/-- Extract the retry owner and certified original prefix from an actual mixed failure. -/
@[expose] def ofFailure (failure : Numerical.Failure input) : Option (Request input) :=
  match failure with
  | .common actualProduction actualNumerical execution stopped returned _ _ _ _ =>
      some ⟨actualProduction, actualNumerical, execution, stopped, returned,
        Numerical.selectedBank input actualProduction, input.rightBank, stopped⟩
  | _ => none

/-- The original pending point and untouched common suffix of this exact retry. -/
abbrev source (retry : Request input) :=
  Points.Resume.computation (depth input retry.production) (left input retry.production) retry.numerical.state.1
    (effectiveLeft input retry.production) (effectiveRight input retry.numerical) input.pointRequest
    retry.savedLeft retry.savedRight retry.stopped

/-- Resume the original pending point and its untouched common suffix. -/
def computation (retry : Request input) :=
  (source input retry).substituteChecked (Numerical.commonHandler input retry.production)

/-- Decode the replies actually supplied to this original retry's mixed source operations. -/
@[expose] def sourceOracle (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    Points.Query → Option (Points.Reply (depth input retry.production)) := fun question =>
  Numerical.commonAnswer input retry.production (oracle (Numerical.commonQuestion input retry.production question))

/-- The outer retry trace is exactly the forwarded original source trace, with each actual reply retained. -/
theorem computation_trace (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((computation input retry).protocol.run oracle).trace =
      ((source input retry).protocol.run (sourceOracle input retry oracle)).trace.map (fun exchange =>
        ⟨Numerical.commonQuestion input retry.production exchange.query,
          oracle (Numerical.commonQuestion input retry.production exchange.query)⟩) := by
  unfold computation
  change (((source input retry).substituteChecked
    (Program.forward (Numerical.commonQuestion input retry.production)
      (fun _ answer => Numerical.commonAnswer input retry.production answer))).protocol.run oracle).trace = _
  exact Program.substituteChecked_forward_trace (Numerical.commonQuestion input retry.production)
    (fun _ answer => Numerical.commonAnswer input retry.production answer) (source input retry) oracle

/-- The displayed outer and original source traces charge exactly the same number of requests. -/
theorem computation_requestCount (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((computation input retry).protocol.run oracle).trace.length =
      ((source input retry).protocol.run (sourceOracle input retry oracle)).trace.length := by
  rw [computation_trace]
  exact Purelib.Data.List.Map.length_map _ _

/-- Carry a pending ball retry with the same original owners and saved point banks. -/
@[expose] def Request.withPending (retry : Request input)
    (next : Stopped input retry.production retry.numerical retry.savedLeft retry.savedRight) : Request input :=
  ⟨retry.production, retry.numerical, retry.execution, retry.original, retry.returned,
    retry.savedLeft, retry.savedRight, next⟩

/-- Carry a later failure with the actual returned pair and the newly retained point banks. -/
@[expose] def Request.withLater (retry : Request input)
    (point : Points.Resume.Pair (depth input retry.production) (left input retry.production) retry.numerical.state.1
      (effectiveLeft input retry.production) (effectiveRight input retry.numerical) input.pointRequest
      retry.stopped.failed)
    (next : Stopped input retry.production retry.numerical retry.stopped.reason.leftBank
      (point.2.val :: retry.stopped.reason.rightBank)) : Request input :=
  ⟨retry.production, retry.numerical, retry.execution, retry.original, retry.returned,
    retry.stopped.reason.leftBank, point.2.val :: retry.stopped.reason.rightBank, next⟩

/-- Continue after a resumed batch using the actual returned point owners and saved original banks. -/
@[expose] def Request.continuation (retry : Request input)
    (point : Points.Resume.Pair (depth input retry.production) (left input retry.production) retry.numerical.state.1
      (effectiveLeft input retry.production) (effectiveRight input retry.numerical) input.pointRequest
      retry.stopped.failed)
    (suffix : Program.CertifiedBatch
      (Independent.Cache.originalChild (left input retry.production) retry.numerical.state.1
        (effectiveLeft input retry.production) (effectiveRight input retry.numerical) input.pointRequest)
      retry.stopped.after)
    (runnerRequest : CertifiedProgram.Request) (count : Nat)
    (productionAccuracy numericalRequest pointRequest : AccuracyRequest) :
    Numerical.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra :=
  let leftPoints := retry.stopped.reason.leftBank ++ suffix.val.map NumericalFrontier.CommonReading.leftPoint
  let rightPoints := point.2.val :: retry.stopped.reason.rightBank ++
    suffix.val.map NumericalFrontier.CommonReading.rightPoint
  ⟨Full.Result.continuation input.production retry.production runnerRequest count productionAccuracy,
    retry.numerical.state, numericalRequest, pointRequest,
    Bank.extendExact retry.production.comparison.receipt pointRequest input.leftBank leftPoints,
    Bank.extend pointRequest input.rightBank rightPoints⟩

/-- Actual completed common readings bound the same recorded production and numerical answers. -/
theorem recorded_difference_le_actual (retry : Request input)
    (common : CommonReadings (left input retry.production) retry.numerical.state.1 input.pointRequest) :
    Fraction.abs (retry.production.recorded.observation.selected.sample.re -
      (integralBound retry.numerical.state.1.cells).midpoint) ≤
        (integralBound retry.production.comparison.left.cells).width +
          (integralBound retry.numerical.state.1.cells).width + common.pointBudget := by
  have selectedSample := (Runner.selected_sample retry.production.recorded).trans
    (congrArg (fun model => model.sample) retry.production.selected_model.symm)
  have savedSample := congrArg (fun receipt => receipt.model.sample) retry.production.comparison_receipt
  rw [selectedSample, ← savedSample]
  exact Source.finite_numerical_answers_difference_le_from_common _ retry.production.comparison.left
    retry.numerical.state.1 input.pointRequest common _ _ retry.production.comparison.leftInside
    (integralBound retry.numerical.state.1.cells).midpoint_contains

/-- The actual resumed common budget is paid by its request and original selected Taylor depth. -/
theorem pointBudget_le (retry : Request input)
    (common : CommonReadings (left input retry.production) retry.numerical.state.1 input.pointRequest) :
    common.pointBudget ≤ input.pointRequest.tolerance + Horner.Real.tailRadius (depth input retry.production) :=
  Source.finite_numerical_pointBudget_le _ common

/-- Original combined replies return the complete original resumed common execution. -/
theorem computation_original (retry : Request input) :
    ((computation input retry).protocol.run (Numerical.originalReply input)).value =
      .ok ((Points.Resume.computation (depth input retry.production) (left input retry.production)
        retry.numerical.state.1 (effectiveLeft input retry.production) (effectiveRight input retry.numerical)
        input.pointRequest retry.savedLeft retry.savedRight retry.stopped).protocol.run
          (fun question => some (Points.original (depth input retry.production) question))) := by
  unfold computation
  apply Program.substituteChecked_value
  intro question
  exact Numerical.commonHandler_original input retry.production question

/-- Exact replay preserves the complete original retry execution and its retained progress. -/
theorem replay (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    (computation input retry).protocol.replayExact ((computation input retry).protocol.run oracle).trace =
      .ok ((computation input retry).protocol.run oracle).value :=
  (computation input retry).protocol.replayExact_run oracle

/-- Changing replies outside the actual retry trace preserves the complete returned work. -/
theorem payload_erasure (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input)
    {Payload : Type} (payload : Payload) (outside : Payload → Numerical.Question input → Numerical.Reply input) :
    (computation input retry).protocol.run (Boundary.Trace.overlay
      ((computation input retry).protocol.run oracle).trace (outside payload)) =
        (computation input retry).protocol.run oracle :=
  (computation input retry).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Retry

end
