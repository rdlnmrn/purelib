module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Full
public import Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Cached
public import Purelib.Integration.Exponential.Real.Observation.Progress
public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Bank

/-!
# Original exponential production and numerical integration comparison

The original production runner and independent numerical history execute
first. Their actual returned finite frontiers then supply the common-point
observer; its returned readings pay for the selected-sample comparison.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Program.Source.Observation.Numerical
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.NumericalFrontier.Continuous.Observation
open Purelib.Integration.NumericalFrontier.Common.Observation
open Purelib.Integration.SourceFrontier

set_option genInjectivity false in
/-- An original production request, a saved numerical history and their point budget. -/
structure Input (policy rightPolicy : Geometry.Policy) (schedule rightSchedule : PositiveStride)
    (extraDepth rightExtra : Nat) where
  /-- The original retained production runner request and any saved comparison. -/ production :
    Full.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra
  /-- The actual saved independent numerical integration state. -/ numerical : Real.integrationProcess.State
  /-- The next original numerical integration request. -/ numericalRequest : AccuracyRequest
  /-- The request used for each mixed common-point observation. -/ pointRequest : AccuracyRequest
  /-- Retained finite-source points with their original selected receipt owners. -/ leftBank :
    List (Bank.ExactPoint production.retained)
  /-- Retained points from the original independent numerical source. -/ rightBank :
    List (NumericalPoint Horner.Real.source)

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

/-- A mixed point operation retains the actual selected production receipt. -/
abbrev CommonQuestion := Full.Selected input.production × Points.Query

/-- Compare mixed operations after identifying the same original selected receipt. -/
instance : DecidableEq (CommonQuestion input) := by
  intro first second
  cases first with
  | mk firstSelected firstQuestion =>
    cases second with
    | mk secondSelected secondQuestion =>
      have same : firstSelected = secondSelected :=
        Subtype.ext (firstSelected.property.trans secondSelected.property.symm)
      cases same
      by_cases equal : firstQuestion = secondQuestion
      · cases equal
        exact isTrue rfl
      · exact isFalse (fun equal' => equal (by cases equal'; rfl))

/-- A mixed point reply retains the same selected finite Taylor owner. -/
abbrev CommonReply := Σ selected : Full.Selected input.production, Points.Reply selected.val.selection.depth

/-- The original production, numerical-history or mixed-point query. -/
abbrev Question := Sum (Full.Question input.production) (Sum Real.Observation.Query (CommonQuestion input))

/-- Distinguish the three original operations and compare their finite questions. -/
instance : DecidableEq (Question input) := by
  intro first second
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      by_cases same : first = second
      · cases same
        exact isTrue rfl
      · exact isFalse (fun equal => same (by cases equal; rfl))
    | inr _ => exact isFalse (fun equal => by cases equal)
  | inr first =>
    cases second with
    | inl _ => exact isFalse (fun equal => by cases equal)
    | inr second =>
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          by_cases same : first = second
          · cases same
            exact isTrue rfl
          · exact isFalse (fun equal => same (by cases equal; rfl))
        | inr _ => exact isFalse (fun equal => by cases equal)
      | inr first =>
        cases second with
        | inl _ => exact isFalse (fun equal => by cases equal)
        | inr second =>
          by_cases same : first = second
          · cases same
            exact isTrue rfl
          · exact isFalse (fun equal => same (by cases equal; rfl))

/-- Each returned reply retains the original operation and its owner. -/
abbrev Reply := Sum (Full.Reply input.production) (Sum Real.Observation.Reply (CommonReply input))

/-- The prepared original numerical history request. -/
abbrev Prepared := Preparation.prepare Horner.Real.modulus input.numericalRequest

/-- The exact original retained numerical point bank for that history request. -/
abbrev NumericalBank := Producer.effectiveBank input.numerical.1
  ((producer Horner.Real.modulus).retainedReadings input.numerical.2)

/-- The complete original numerical history execution returned by its Gaussian lowering. -/
abbrev HistoryExecution := Basic.Execution (Continuation.Query (Prepared input))
  (Continuation.Reply (Prepared input) (NumericalBank input) input.numericalRequest)
  (Except (Continuation.Failure (Prepared input)) Real.integrationProcess.State)

set_option genInjectivity false in
/-- An actual successful numerical history and its returned next state. -/
structure NumericalDone where
  /-- The original ordered numerical history execution. -/ execution : HistoryExecution input
  /-- Its actual next persistent state. -/ state : Real.integrationProcess.State
  /-- The same execution returned that state. -/ value_eq : execution.value = .ok state

/-- The exact returned production frontier viewed through its cached numerical point processes. -/
abbrev exactFrontier (production : Full.Result input.production) :=
  SourceFrontier.Numerical.frontier production.comparison.left input.pointRequest

/-- The original selected receipt carried by the production comparison. -/
@[expose] def selected (production : Full.Result input.production) : Full.Selected input.production :=
  ⟨production.comparison.receipt, production.comparison_receipt.trans production.selected.property⟩

/-- The supplied points belonging to the actual returned selected receipt. -/
abbrev selectedBank (production : Full.Result input.production) :=
  Bank.forReceipt production.comparison.receipt input.leftBank

/-- The first failed common occurrence and all work returned before it. -/
abbrev CommonFailure (production : Full.Result input.production) (numerical : NumericalDone input) :=
  Independent.Cache.BatchStopped (exactFrontier input production) numerical.state.1
    (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
    (Independent.Cache.rightAvailable numerical.state.1 input.rightBank) input.pointRequest
    (selectedBank input production) input.rightBank
    (Points.Cached.ProgressFailure production.comparison.receipt.selection.depth
      (exactFrontier input production) numerical.state.1
      (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
      (Independent.Cache.rightAvailable numerical.state.1 input.rightBank) input.pointRequest)

/-- The complete actual banked common-point execution over its original source operations. -/
abbrev CommonExecution (production : Full.Result input.production) (numerical : NumericalDone input) :=
  Basic.Execution Points.Query (Option (Points.Reply production.comparison.receipt.selection.depth))
    (Except (CommonFailure input production numerical)
      (CommonReadings (exactFrontier input production) numerical.state.1 input.pointRequest))

set_option genInjectivity false in
/-- The original tagged numerical operation failed at its actual outer or Gaussian boundary. -/
inductive NumericalSourceFailure where
  /-- The displayed numerical operation received a different outer operation's reply. -/ | operation
      (question : Real.Observation.Query)
  /-- The original tagged Gaussian point or operation was invalid. -/ | gaussian
      (failure : Real.Observation.Failure)

/-- The original stopped numerical history and its question-owned partial work. -/
abbrev NumericalStop := Real.Observation.Progress.HistoryStop input.numerical input.numericalRequest
  NumericalSourceFailure

/-- The actual displayed tagged execution of the progress-bearing numerical history. -/
abbrev NumericalProgressExecution := Basic.Execution (Question input) (Reply input)
  (Except (NumericalStop input) (HistoryExecution input))

set_option genInjectivity false in
/-- The first failed operation with all already completed original owners. -/
inductive Failure where
  /-- A production operation received another operation's reply. -/ | productionOperation
      (question : Full.Question input.production)
  /-- The original production runner returned this failure. -/ | production (failure : Full.Failure input.production)
  /-- A tagged numerical operation failed with its actual stopped continuation and displayed trace. -/ | numericalStop
      (production : Full.Result input.production) (execution : NumericalProgressExecution input)
      (stopped : NumericalStop input) (returned : execution.value = .error stopped)
  /-- The original numerical history rejected its actual returned observations. -/ | numericalHistory
      (production : Full.Result input.production) (execution : HistoryExecution input)
      (failure : Continuation.Failure (Prepared input)) (value_eq : execution.value = .error failure)
  /-- The original common-point request failed with its actual completed points and retained banks. -/ | common
      (production : Full.Result input.production) (numerical : NumericalDone input)
      (execution : CommonExecution input production numerical)
      (failure : CommonFailure input production numerical) (value_eq : execution.value = .error failure)
      (leftBank : List (Bank.ExactPoint input.production.retained))
      (left_eq : leftBank = Bank.extendExact production.comparison.receipt input.pointRequest
        input.leftBank failure.reason.leftAdded)
      (rightBank : List (NumericalPoint Horner.Real.source))
      (right_eq : rightBank = Bank.extend input.pointRequest input.rightBank failure.reason.rightAdded)

set_option genInjectivity false in
/-- Both actual original executions, their common readings and updated original-owner point banks. -/
structure Result where
  /-- The actual original production runner and its retained selected frontier. -/ production :
    Full.Result input.production
  /-- The actual continued independent numerical history. -/ numerical : NumericalDone input
  /-- The actual ordered common-source observation execution. -/ commonExecution :
    CommonExecution input production numerical
  /-- The actual returned mixed common readings of those exact frontiers. -/ common :
    CommonReadings (exactFrontier input production) numerical.state.1 input.pointRequest
  /-- The retained common execution returned these same readings. -/ common_eq : commonExecution.value = .ok common
  /-- Actual finite-source observations retained under the selected receipt. -/ leftBank :
    List (Bank.ExactPoint input.production.retained)
  /-- The left bank retains exactly the useful returned observations and original bank. -/ left_eq :
    leftBank = Bank.extendExact production.comparison.receipt input.pointRequest input.leftBank
      (common.readings.map CommonReading.leftPoint)
  /-- Actual independent numerical observations retained from the common reading. -/ rightBank :
    List (NumericalPoint Horner.Real.source)
  /-- The right bank retains exactly the useful returned observations and original bank. -/ right_eq :
    rightBank = Bank.extend input.pointRequest input.rightBank (common.readings.map CommonReading.rightPoint)

/-- Answer each original operation from its exact production, Gaussian or selected finite source. -/
@[expose] def originalReply : Question input → Reply input
  | .inl question => .inl (Full.originalReply input.production question)
  | .inr (.inl question) => .inr (.inl (Real.Observation.original question))
  | .inr (.inr (receipt, question)) => .inr (.inr ⟨receipt, Points.original receipt.val.selection.depth question⟩)

/-- Forward one original production operation. -/
private def productionHandler (question : Full.Question input.production) :
    Program (Question input) (Reply input) (Except (Failure input) (Full.Reply input.production)) :=
  .request (.inl question) fun answer => match answer with
    | .inl reply => .pure (.ok reply)
    | .inr _ => .pure (.error (.productionOperation question))

/-- Observe the complete original production runner. -/
def productionProgram := (Full.computation input.production).substituteChecked (productionHandler input)

/-- Forward an original numerical operation and identify any wrong outer reply at that operation. -/
@[expose] def numericalHandler (question : Real.Observation.Query) :
    Program (Question input) (Reply input) (Except NumericalSourceFailure Real.Observation.Reply) :=
  .request (.inr (.inl question)) fun answer => match answer with
    | .inr (.inl reply) => .pure (.ok reply)
    | _ => .pure (.error (.operation question))

/-- Original combined replies forward each original tagged Gaussian numerical reply. -/
theorem numericalHandler_original (question : Real.Observation.Query) :
    ((numericalHandler input question).protocol.run (originalReply input)).value =
      .ok (Real.Observation.original question) := rfl

/-- Observe the original numerical history while retaining any stopped continuation. -/
def numericalProgram := Real.Observation.Progress.historyWith (numericalHandler input) NumericalSourceFailure.gaussian
  input.numerical input.numericalRequest

/-- Record the actual tagged history execution, including its first failed operation. -/
def numericalRecording := (numericalProgram input).substituteChecked (Program.forward id (fun _ reply => reply))

/-- The actual combined question for one selected mixed source operation. -/
@[expose] def commonQuestion (production : Full.Result input.production) (question : Points.Query) : Question input :=
  .inr (.inr (selected input production, question))

/-- Decode a mixed source reply only for its actual original selected receipt. -/
@[expose] def commonAnswer (production : Full.Result input.production) (answer : Reply input) :
    Option (Points.Reply production.comparison.receipt.selection.depth) :=
  let owner := selected input production
  match answer with
  | .inr (.inr ⟨reported, reply⟩) => by
      have same : reported = owner := Subtype.ext (reported.property.trans owner.property.symm)
      cases same
      exact some reply
  | _ => none

/-- Forward a mixed point operation and retain a wrong operation as a missing point reply.

The cached pair program handles that failure at the original occurrence, so
it can retain previously returned observations and any completed left point. -/
@[expose] def commonHandler (production : Full.Result input.production) : Points.Query →
    Program (Question input) (Reply input)
      (Except Empty (Option (Points.Reply production.comparison.receipt.selection.depth))) :=
  Program.forward (commonQuestion input production) (fun _ answer => commonAnswer input production answer)

/-- Original combined replies forward the original selected finite or Gaussian point reply. -/
theorem commonHandler_original (production : Full.Result input.production) (question : Points.Query) :
    ((commonHandler input production question).protocol.run (originalReply input)).value =
      .ok (some (Points.original production.comparison.receipt.selection.depth question)) := by
  unfold commonHandler Program.forward commonQuestion commonAnswer
  rfl

/-- Observe common points of the two actual returned frontiers using both retained banks. -/
def commonProgram (production : Full.Result input.production) (numerical : NumericalDone input) :=
  (Points.Cached.computationProgress production.comparison.receipt.selection.depth (exactFrontier input production)
    numerical.state.1 (selectedBank input production) input.rightBank input.pointRequest).substituteChecked
      (commonHandler input production)

/-- Assemble the actual common execution or preserve its exact typed failure and point banks. -/
def commonFinish (production : Full.Result input.production) (numerical : NumericalDone input) :
    Program (Question input) (Reply input) (Except (Failure input) (Result input)) :=
  (commonProgram input production numerical).map fun commonResult =>
    match commonResult with
    | .error impossible => nomatch impossible
    | .ok execution =>
        match common_eq : execution.value with
        | .error failure =>
            let leftBank := Bank.extendExact production.comparison.receipt input.pointRequest
              input.leftBank failure.reason.leftAdded
            let rightBank := Bank.extend input.pointRequest input.rightBank
              failure.reason.rightAdded
            .error (.common production numerical execution failure common_eq
              leftBank rfl rightBank rfl)
        | .ok common =>
            let leftBank := Bank.extendExact production.comparison.receipt input.pointRequest
              input.leftBank (common.readings.map CommonReading.leftPoint)
            let rightBank := Bank.extend input.pointRequest input.rightBank
              (common.readings.map CommonReading.rightPoint)
            .ok ⟨production, numerical, execution, common, common_eq, leftBank, rfl,
              rightBank, rfl⟩

/-- Compose the original runner, continued numerical history and their actual common-point observations. -/
@[expose] def computation : Program (Question input) (Reply input) (Except (Failure input) (Result input)) :=
  (productionProgram input).bind fun productionResult =>
    match productionResult with
    | .error failure => .pure (.error failure)
    | .ok productionExecution =>
        match productionExecution.value with
        | .error failure => .pure (.error (.production failure))
        | .ok production =>
            (numericalRecording input).bind fun numericalResult =>
              match numericalResult with
              | .error impossible => nomatch impossible
              | .ok numericalExecution =>
                  match returned : numericalExecution.value with
                  | .error stopped => .pure (.error (.numericalStop production numericalExecution stopped returned))
                  | .ok history =>
                      match success : history.value with
                      | .error failure => .pure (.error (.numericalHistory production history failure success))
                      | .ok state =>
                          let numerical : NumericalDone input := ⟨history, state, success⟩
                          commonFinish input production numerical

/-- Original replies preserve the complete original production execution. -/
private theorem productionProgram_original :
    ((productionProgram input).protocol.run (originalReply input)).value =
      .ok ((Full.computation input.production).protocol.run (Full.originalReply input.production)) := by
  unfold productionProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Original replies preserve the complete actual progress-bearing numerical history. -/
private theorem numericalRecording_original :
    ((numericalRecording input).protocol.run (originalReply input)).value =
      .ok ((numericalProgram input).protocol.run (originalReply input)) := by
  unfold numericalRecording
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Original tagged replies return the exact original numerical-history execution. -/
private theorem numericalProgram_original :
    ((numericalProgram input).protocol.run (originalReply input)).value =
      .ok ((Continuation.historyComputation Horner.Real.modulus input.numerical input.numericalRequest).protocol.run
        (Continuation.originalReplyAll (Prepared input) (NumericalBank input) input.numericalRequest)) := by
  unfold numericalProgram
  exact Real.Observation.Progress.historyWith_original (numericalHandler input) NumericalSourceFailure.gaussian
    input.numerical input.numericalRequest (originalReply input) (numericalHandler_original input)

/-- Original replies preserve the complete actual banked common-point execution. -/
private theorem commonProgram_original (production : Full.Result input.production) (numerical : NumericalDone input) :
    ((commonProgram input production numerical).protocol.run (originalReply input)).value =
      .ok ((Points.Cached.computationProgress production.comparison.receipt.selection.depth
        (exactFrontier input production) numerical.state.1 (selectedBank input production) input.rightBank
        input.pointRequest).protocol.run
          (fun question => some (Points.original production.comparison.receipt.selection.depth question))) := by
  unfold commonProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Original replies complete the common comparison of the supplied actual owners.

The common readings are built from the supplied production frontier and
numerical state, including both retained banks. No claim is made about how
either owner was obtained.
-/
theorem commonFinish_original (production : Full.Result input.production) (numerical : NumericalDone input) :
    ∃ result : Result input,
      ((commonFinish input production numerical).protocol.run (originalReply input)).value = .ok result ∧
      result.production = production ∧ result.numerical = numerical ∧
      result.commonExecution =
        (Points.Cached.computationProgress result.production.comparison.receipt.selection.depth
          (exactFrontier input result.production) result.numerical.state.1 (selectedBank input result.production)
          input.rightBank input.pointRequest).protocol.run
            (fun question => some (Points.original result.production.comparison.receipt.selection.depth question)) ∧
      result.common = Common.Cache.commonReadings (exactFrontier input result.production)
        result.numerical.state.1
        (Independent.Cache.leftAvailable (exactFrontier input result.production) (selectedBank input result.production))
        (Independent.Cache.rightAvailable result.numerical.state.1 input.rightBank) input.pointRequest := by
  unfold commonFinish
  rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
  dsimp only
  have commonValue := Points.Cached.computationProgress_original production.comparison.receipt.selection.depth
    (exactFrontier input production) numerical.state.1 (selectedBank input production) input.rightBank
    input.pointRequest
  split
  next failure failed =>
    have impossible : Except.error failure = .ok (Common.Cache.commonReadings
        (exactFrontier input production) numerical.state.1
        (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
        (Independent.Cache.rightAvailable numerical.state.1 input.rightBank) input.pointRequest) :=
      failed.symm.trans commonValue
    cases impossible
  next common success =>
    have common_eq : common = Common.Cache.commonReadings
        (exactFrontier input production) numerical.state.1
        (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
        (Independent.Cache.rightAvailable numerical.state.1 input.rightBank) input.pointRequest :=
      Except.ok.inj (success.symm.trans commonValue)
    exact ⟨_, rfl, rfl, rfl, rfl, common_eq⟩

/-- Original replies return the original production, numerical history and actual bank-selected common readings. -/
theorem computation_original :
    ∃ result : Result input,
      ((computation input).protocol.run (originalReply input)).value = .ok result ∧
      result.production.recorded = Record.record input.production.retained.program
        input.production.request input.production.count ∧
      result.numerical.state = Real.integrationProcess.request input.numerical
        input.numericalRequest.tolerance input.numericalRequest.positive ∧
      result.numerical.execution =
        (Continuation.historyComputation Horner.Real.modulus input.numerical input.numericalRequest).protocol.run
          (Continuation.originalReplyAll (Prepared input) (NumericalBank input) input.numericalRequest) ∧
      result.commonExecution =
        (Points.Cached.computationProgress result.production.comparison.receipt.selection.depth
          (exactFrontier input result.production) result.numerical.state.1 (selectedBank input result.production)
          input.rightBank input.pointRequest).protocol.run
            (fun question => some (Points.original result.production.comparison.receipt.selection.depth question)) ∧
      result.common = Common.Cache.commonReadings (exactFrontier input result.production)
        result.numerical.state.1
        (Independent.Cache.leftAvailable (exactFrontier input result.production) (selectedBank input result.production))
        (Independent.Cache.rightAvailable result.numerical.state.1 input.rightBank) input.pointRequest := by
  obtain ⟨production, productionValue, recorded⟩ := Full.computation_original input.production
  have historyValue := Continuation.historyComputation_original Horner.Real.modulus
    input.numerical input.numericalRequest
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, productionProgram_original]
  dsimp only
  rw [productionValue]
  rw [Program.bind_execution, Protocol.bind_run_value, numericalRecording_original]
  dsimp only
  have originalHistory := numericalProgram_original input
  split
  next stopped failed =>
    have impossible : Except.error stopped = Except.ok
        ((Continuation.historyComputation Horner.Real.modulus input.numerical input.numericalRequest).protocol.run
          (Continuation.originalReplyAll (Prepared input) (NumericalBank input) input.numericalRequest)) :=
      failed.symm.trans originalHistory
    cases impossible
  next history returned =>
    have history_eq : history =
        (Continuation.historyComputation Horner.Real.modulus input.numerical input.numericalRequest).protocol.run
          (Continuation.originalReplyAll (Prepared input) (NumericalBank input) input.numericalRequest) :=
      Except.ok.inj (returned.symm.trans originalHistory)
    cases history_eq
    split
    next failure failed =>
      have impossible : Except.error failure = .ok (Real.integrationProcess.request input.numerical
          input.numericalRequest.tolerance input.numericalRequest.positive) := failed.symm.trans historyValue
      cases impossible
    next state success =>
      have state_eq : state = Real.integrationProcess.request input.numerical
          input.numericalRequest.tolerance input.numericalRequest.positive :=
        Except.ok.inj (success.symm.trans historyValue)
      unfold commonFinish
      rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
      dsimp only
      have commonValue := Points.Cached.computationProgress_original production.comparison.receipt.selection.depth
        (exactFrontier input production) state.1 (selectedBank input production) input.rightBank input.pointRequest
      split
      next failure failed =>
        have impossible : Except.error failure = .ok (Common.Cache.commonReadings
            (exactFrontier input production) state.1
            (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
            (Independent.Cache.rightAvailable state.1 input.rightBank) input.pointRequest) :=
          failed.symm.trans commonValue
        cases impossible
      next common success =>
        have common_eq : common = Common.Cache.commonReadings
            (exactFrontier input production) state.1
            (Independent.Cache.leftAvailable (exactFrontier input production) (selectedBank input production))
            (Independent.Cache.rightAvailable state.1 input.rightBank) input.pointRequest :=
          Except.ok.inj (success.symm.trans commonValue)
        exact ⟨_, rfl, recorded, state_eq, rfl, rfl, common_eq⟩

/-- Continue both actual returned owners with the retained mixed point banks. -/
@[expose] def Result.continuation (result : Result input) (runnerRequest : CertifiedProgram.Request)
    (count : Nat) (productionAccuracy numericalRequest pointRequest : AccuracyRequest) :
    Input policy rightPolicy schedule rightSchedule extraDepth rightExtra :=
  ⟨Full.Result.continuation input.production result.production runnerRequest count productionAccuracy,
    result.numerical.state,
    numericalRequest, pointRequest, result.leftBank, result.rightBank⟩

/-- Resume a failed common-point attempt using its actual returned owners and partial point banks. -/
@[expose] def Failure.continuation (failure : Failure input) (runnerRequest : CertifiedProgram.Request)
    (count : Nat) (productionAccuracy numericalRequest pointRequest : AccuracyRequest) :
    Option (Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :=
  match failure with
  | .common actualProduction actualNumerical _ _ _ leftBank _ rightBank _ =>
      some ⟨Full.Result.continuation input.production actualProduction runnerRequest count productionAccuracy,
        actualNumerical.state,
        numericalRequest, pointRequest, leftBank, rightBank⟩
  | _ => none

/-- Every actual successful comparison pays for the returned production sample and numerical midpoint. -/
theorem Result.selected_difference_le_actual (result : Result input) :
    Fraction.abs (result.production.comparison.receipt.model.sample.re -
      (integralBound result.numerical.state.1.cells).midpoint) ≤
        (integralBound result.production.comparison.left.cells).width +
          (integralBound result.numerical.state.1.cells).width + result.common.pointBudget :=
  Source.finite_numerical_answers_difference_le_from_common _ result.production.comparison.left
    result.numerical.state.1 input.pointRequest result.common _ _ result.production.comparison.leftInside
    (integralBound result.numerical.state.1.cells).midpoint_contains

/-- The same actual common readings bound the original runner's recorded integration sample. -/
theorem Result.recorded_difference_le_actual (result : Result input) :
    Fraction.abs (result.production.recorded.observation.selected.sample.re -
      (integralBound result.numerical.state.1.cells).midpoint) ≤
        (integralBound result.production.comparison.left.cells).width +
          (integralBound result.numerical.state.1.cells).width + result.common.pointBudget := by
  have selectedSample := (Runner.selected_sample result.production.recorded).trans
    (congrArg (fun model => model.sample) result.production.selected_model.symm)
  have savedSample := congrArg (fun receipt => receipt.model.sample) result.production.comparison_receipt
  rw [selectedSample, ← savedSample]
  exact result.selected_difference_le_actual

/-- The actual returned common-point budget is paid by the request and returned selected depth. -/
theorem Result.pointBudget_le (result : Result input) :
    result.common.pointBudget ≤ input.pointRequest.tolerance +
      Horner.Real.tailRadius result.production.comparison.receipt.selection.depth :=
  Source.finite_numerical_pointBudget_le _ result.common

/-- Exact replay preserves every actual success or first typed failure. -/
theorem computation_replay (oracle : Question input → Reply input) :
    (computation input).protocol.replayExact ((computation input).protocol.run oracle).trace =
      .ok ((computation input).protocol.run oracle).value :=
  (computation input).protocol.replayExact_run oracle

/-- Changing replies outside the actual combined trace preserves its complete execution. -/
theorem payload_erasure {Payload : Type} (oracle : Question input → Reply input) (payload : Payload)
    (outside : Payload → Question input → Reply input) :
    (computation input).protocol.run (Boundary.Trace.overlay
      ((computation input).protocol.run oracle).trace (outside payload)) = (computation input).protocol.run oracle :=
  (computation input).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical

end
