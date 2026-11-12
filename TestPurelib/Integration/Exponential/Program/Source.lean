module
import Purelib.Integration.Exponential.Program.Source
import Purelib.Integration.Exponential.Program.Source.Comparison
import Purelib.Integration.Exponential.Program.Source.Observation
import Purelib.Integration.Exponential.Program.Source.Observation.StageComparison
import Purelib.Integration.Exponential.Program.Source.Observation.Runner
public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Full
import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Paired
import Purelib.Integration.Exponential.Real

/-! Original cached exponential stages retain their own source-linked enclosures. -/

namespace TestPurelib.Integration.Exponential.Program.Source

open Purelib.Approximation
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Real
open Purelib.Integration.Exponential.Real.Observation (original)
open Purelib.Integration.Exponential.Program
open Purelib.Integration.Exponential.Program.Source.Observation
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query.Program
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

/-- Distinct original geometry policies and positive-stride schedules. -/
@[expose] public def firstPolicy : Geometry.Policy := Geometry.Policy.fixedCuts []
/-- A distinct geometry with one interior cut. -/
@[expose] public def secondPolicy : Geometry.Policy := Geometry.Policy.fixedCuts [1 / 2]
/-- The first exponential stage schedule. -/
@[expose] public def firstSchedule : PositiveStride := ⟨0, 0⟩
/-- The second exponential stage schedule. -/
@[expose] public def secondSchedule : PositiveStride := ⟨1, 1⟩

/-- Independent requests for the original program stages. -/
@[expose] public def firstRequest : AccuracyRequest := ⟨8, by decide⟩
/-- The accuracy request for the second stage. -/
@[expose] public def secondRequest : AccuracyRequest := ⟨4, by decide⟩
/-- The original first exponential stage and its source frontier. -/
@[expose] public def first := Program.Source.build firstPolicy firstSchedule 0 0 firstRequest
private def second := Program.Source.build secondPolicy secondSchedule 0 1 secondRequest

/-- The original selected stage with its displayed finite Taylor source reads. -/
private def firstObservation := Source.Observation.computation firstPolicy firstSchedule 0 0 firstRequest
private def firstPreparation := Source.Observation.preparation firstPolicy firstSchedule 0 firstRequest
private def firstOracle := SourceFrontier.Continuous.Observation.originalReply firstPreparation

/-- Independently retained original exponential programs for a source-linked stage comparison. -/
@[expose] public def firstRetained := Program.Retained.canonical firstPolicy firstSchedule 0
/-- The second policy's retained exponential program. -/
@[expose] public def secondRetained := Program.Retained.canonical secondPolicy secondSchedule 0
private def firstStageRequest := StageComparison.Request.make firstRetained 0 firstRequest
/-- The second retained stage and its source request. -/
@[expose] public def secondStageRequest := StageComparison.Request.make secondRetained 1 secondRequest
private def stageComparison := StageComparison.computation firstStageRequest secondStageRequest
private def stageOracle := StageComparison.originalReply firstStageRequest secondStageRequest

/-- The original finite integration observation and its source comparison. -/
@[expose] public def runnerRequest : CertifiedProgram.Request := ⟨0, 1, by decide⟩
private def runnerPrepared := Runner.prepare firstRetained runnerRequest 2
private def runnerComparison := Runner.computation runnerPrepared firstRequest secondStageRequest
private def runnerOracle := Runner.originalReply runnerPrepared firstRequest secondStageRequest

/-- The original runner's model-query program lowered through retained indexed model receipts. -/
private def modelOriginal := Expansion.program (control firstRetained.program) runnerRequest 2
private def modelObservation := Runner.Model.receiptComputation firstRetained [] modelOriginal
private def modelOracle (index : Nat) := some (Runner.Model.originalReply firstRetained index)

/-- The original runner and both source owners in one actual query execution. -/
@[expose] public def fullInput : Runner.Full.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0 :=
  ⟨firstRetained, [], runnerRequest, 2, firstRequest, secondStageRequest, []⟩
private def fullProgram := Runner.Full.computation fullInput
private def fullOracle := Runner.Full.originalReply fullInput

example := Runner.Full.computation_original fullInput
example := Runner.Full.computation_replay fullInput fullOracle
example := Runner.Paired.computation_original fullInput
example := Runner.Paired.computation_replay fullInput

example (result : Runner.Full.Result fullInput) :
    result.recorded.observation.selected.sample =
      result.comparison.leftAnchor.program.approximation.sample result.comparison.receipt.index :=
  Runner.Full.Result.selected_sample_approximation fullInput result

example (result : Runner.Full.Result fullInput) :
    result.recorded.observation.selected.sample =
      Sample.sample 1 (result.selected.val.selection.depth + 1) - 1 :=
  Runner.Full.Result.selected_sample_taylor fullInput result

example (result : Runner.Full.Result fullInput) :
    Gaussian.Equivalence.NamedEquivalent result.comparison.leftAnchor.program.output.name
      Exponential.Equivalence.Reference.exponentialMinusOne :=
  Runner.Full.Result.output_equivalent_existing fullInput result

example (selected : Runner.Full.Selected fullInput)
    (point : SourcePoint (Runner.Full.selectedRequest fullInput selected).source)
    (numerical : NumericalPoint Real.source) (unit : 0 ≤ numerical.point ∧ numerical.point ≤ 1)
    (paired : Paired.PointState numerical unit) (same : point.point = numerical.point) :=
  Runner.Paired.selectedSample_numerical_midpoint_normSq_le fullInput selected point numerical unit paired same

example (selected : Runner.Full.Selected fullInput) (point : SourcePoint fullInput.right.source)
    (numerical : NumericalPoint Real.source) (unit : 0 ≤ numerical.point ∧ numerical.point ≤ 1)
    (paired : Paired.PointState numerical unit) (same : point.point = numerical.point) :=
  Runner.Paired.rightSample_numerical_midpoint_normSq_le fullInput selected point numerical unit paired same

example := Certified.Cache.computation_original
  (Runner.Model.receiptSource firstRetained) (Runner.Model.originalReply firstRetained) (fun _ => rfl) modelOriginal []

example := Certified.Cache.computation_replay
  (Runner.Model.receiptSource firstRetained) [] modelOriginal modelOracle

example : (runnerComparison.protocol.run runnerOracle).value =
    .ok (StageComparison.canonical (Runner.stageRequest runnerPrepared firstRequest)
      secondStageRequest) :=
  Runner.computation_original runnerPrepared firstRequest secondStageRequest

example : runnerComparison.protocol.replayExact (runnerComparison.protocol.run runnerOracle).trace =
    .ok (.ok (StageComparison.canonical (Runner.stageRequest runnerPrepared firstRequest)
      secondStageRequest)) :=
  Runner.computation_replay runnerPrepared firstRequest secondStageRequest

example : (stageComparison.protocol.run stageOracle).value =
    .ok (StageComparison.canonical firstStageRequest secondStageRequest) :=
  StageComparison.computation_original firstStageRequest secondStageRequest

example : stageComparison.protocol.replayExact (stageComparison.protocol.run stageOracle).trace =
    .ok (.ok (StageComparison.canonical firstStageRequest secondStageRequest)) :=
  StageComparison.computation_replay firstStageRequest secondStageRequest

example (compared : StageComparison.Compared firstStageRequest secondStageRequest) :
    Fraction.abs (compared.leftStage.stage.sample.re - compared.rightStage.stage.sample.re) ≤
      (integralBound (StageComparison.retainedFrontier firstStageRequest
        compared.leftStage).cells).width +
        (integralBound (StageComparison.retainedFrontier secondStageRequest
          compared.rightStage).cells).width + compared.common.val.pointBudget :=
  StageComparison.Compared.samples_difference_le firstStageRequest secondStageRequest compared

example (compared : StageComparison.Compared firstStageRequest secondStageRequest) :
    compared.leftStage.stage = firstStageRequest.stage :=
  StageComparison.Compared.left_stage firstStageRequest secondStageRequest compared

example : (firstObservation.protocol.run firstOracle).value = .ok first :=
  Source.Observation.computation_original firstPolicy firstSchedule 0 0 firstRequest

example : firstObservation.protocol.replayExact (firstObservation.protocol.run firstOracle).trace = .ok (.ok first) :=
  Source.Observation.computation_replay firstPolicy firstSchedule 0 0 firstRequest

example : first.stage = first.program.stage 0 := first.stage_eq

example : second.stage = second.program.stage 1 := second.stage_eq

example : (integralBound first.sourceResult.frontier.cells).Contains first.stage.sample.re := first.sample_inside

example : (first.advanceFrontier first.sourceResult.frontier [] firstRequest).frontier =
    first.sourceResult.frontier := by
  have adequate := first.sourceResult.accurate
  rw [first.request_eq] at adequate
  rw [first.advanceFrontier_reused first.sourceResult.frontier [] firstRequest adequate]
  rfl

example : (first.advanceFrontier first.sourceResult.frontier [] secondRequest).request = secondRequest :=
  first.advanceFrontier_request first.sourceResult.frontier [] secondRequest

example : ((Source.Observation.continuation first first.sourceResult.frontier [] secondRequest).protocol.run
    (SourceFrontier.Continuous.Observation.Continuation.originalReplyAll
      (Source.Observation.preparation firstPolicy firstSchedule 0 secondRequest))).value =
        .ok (first.advanceFrontier first.sourceResult.frontier [] secondRequest) :=
  Source.Observation.continuation_original first first.sourceResult.frontier [] secondRequest

example := Source.Observation.continuation_replay first first.sourceResult.frontier [] secondRequest

example : (integralBound (first.advanceFrontier first.sourceResult.frontier [] secondRequest).frontier.cells).Contains
    first.stage.sample.re := first.advanceFrontier_sample_contains first.sourceResult.frontier [] secondRequest

example (insufficient : ¬ (integralBound first.sourceResult.frontier.cells).width < secondRequest.tolerance) :
    match first.advanceFrontier first.sourceResult.frontier [] secondRequest with
    | .reused _ _ => False
    | .refined _ retained _ _ _ _ => retained = [] :=
  first.advanceFrontier_cached first.sourceResult.frontier [] secondRequest insufficient

example : first.stage.sample.im = 0 := first.sample_im_zero

example : second.stage.sample.im = 0 := second.sample_im_zero

example : (integralBound second.sourceResult.frontier.cells).Contains second.stage.sample.re := second.sample_inside

example : Fraction.abs (first.stage.sample.re - second.stage.sample.re) ≤
    (integralBound first.sourceResult.frontier.cells).width + (integralBound second.sourceResult.frontier.cells).width +
      (Program.Source.common first second).pointBudget := Program.Source.samples_difference_le first second

example : Real.tailRadius 0 = 4 ∧ Real.tailRadius 3 = (1 / 2 : Fraction.Rational) := by decide +kernel

example : Fraction.abs (first.stage.sample.re - second.stage.sample.re) ≤
    (integralBound first.sourceResult.frontier.cells).width + (integralBound second.sourceResult.frontier.cells).width +
      (Real.tailRadius (Selection.selection firstPolicy firstSchedule 0).depth +
        Real.tailRadius (Selection.selection secondPolicy secondSchedule 1).depth) :=
  Program.Source.samples_difference_le_radii first second

/-- Return a successful finite observation or report its original failure context. -/
private def requireSuccess {Error Value : Type} (message : String) (result : Except Error Value) : IO Value :=
  match result with
  | .error _ => throw (IO.userError message)
  | .ok value => pure value

/-- Exercise saved, refined and changed-stage continuations beyond the retained model prefix. -/
private def checkLateStages : IO Unit := do
  let lateRequest : CertifiedProgram.Request := ⟨64, 1, by decide⟩
  let lateInput : Runner.Full.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0 :=
    ⟨firstRetained, [], lateRequest, 1, firstRequest, secondStageRequest, []⟩
  let lateProgram := Runner.Full.computation lateInput
  let lateExecution := lateProgram.protocol.run (Runner.Full.originalReply lateInput)
  match lateExecution.value with
  | .error _ => throw (IO.userError "out-of-prefix exponential runner failed")
  | .ok result =>
      unless result.selected.val.index ≥ 64 &&
          result.comparison.leftAnchor.stage.sample == result.selected.val.model.sample &&
          !result.comparison.common.val.readings.isEmpty do
        throw (IO.userError "out-of-prefix exponential runner lost its actual selected stage or common readings")
      let misses := lateExecution.trace.filterMap fun exchange =>
        match exchange.query with
        | .inl index => some index
        | .inr _ => none
      let occurrences := result.recorded.trace.map fun exchange => exchange.query
      unless misses == [64] && occurrences.take 2 == [64, 64] do
        throw (IO.userError "out-of-prefix repeated model occurrence was not reused")
      let resumedInput := Runner.Full.Result.continuation lateInput result lateRequest 1 firstRequest
      let resumed := (Runner.Full.computation resumedInput).protocol.run (Runner.Full.originalReply resumedInput)
      let resumedMisses := resumed.trace.filterMap fun exchange =>
        match exchange.query with
        | .inl index => some index
        | .inr _ => none
      match resumed.value with
      | .error _ => throw (IO.userError "out-of-prefix exponential continuation failed")
      | .ok resumedResult =>
          unless resumedMisses.isEmpty && (resumedResult.recorded.trace.map (fun exchange => exchange.query)).take 2 ==
              [64, 64] && resumed.trace.isEmpty &&
              resumedResult.completed.bank.map (fun receipt => receipt.index) == [64] do
            throw (IO.userError "continued exponential runner did not reuse its model bank and saved comparison")
          match resumedResult.progress with
          | .reused _ _ _ _ =>
              let nextInput := Runner.Full.Result.continuation resumedInput resumedResult lateRequest 1 firstRequest
              unless nextInput.saved.length == resumedInput.saved.length do
                throw (IO.userError "reusing a source comparison duplicated its retained history")
          | _ => throw (IO.userError "adequate saved source comparison was not retained")
      let savedOnlyInput := { resumedInput with bank := [] }
      let savedOnly := (Runner.Full.computation savedOnlyInput).protocol.run (Runner.Full.originalReply savedOnlyInput)
      match savedOnly.value with
      | .error _ => throw (IO.userError "saved-only exponential continuation failed")
      | .ok savedOnlyResult =>
          unless savedOnly.trace.isEmpty && savedOnlyResult.completed.bank.map (fun receipt => receipt.index) == [64] do
            throw (IO.userError "saved comparison did not supply its actual model receipt")
      let looseAccuracy : AccuracyRequest := ⟨16, by decide⟩
      let looseInput := Runner.Full.Result.continuation lateInput result lateRequest 1 looseAccuracy
      let loose := (Runner.Full.computation looseInput).protocol.run (Runner.Full.originalReply looseInput)
      match loose.value with
      | .error _ => throw (IO.userError "looser exponential source continuation failed")
      | .ok looseResult =>
          match looseResult.progress with
          | .reused _ _ _ _ =>
              unless loose.trace.isEmpty &&
                  decide ((integralBound looseResult.comparison.left.cells).width < looseAccuracy.tolerance) do
                throw (IO.userError "looser source request failed to reuse the actual saved comparison")
          | _ => throw (IO.userError "looser source request reconstructed the saved comparison")
      let tightAccuracy : AccuracyRequest := ⟨1, by decide⟩
      let tightInput := Runner.Full.Result.continuation lateInput result lateRequest 1 tightAccuracy
      let tightExecution := (Runner.Full.computation tightInput).protocol.run (Runner.Full.originalReply tightInput)
      let tightResult ← requireSuccess "tighter exponential source continuation failed" tightExecution.value
      let oldTags := result.comparison.leftBank.map fun point => point.point
      let refinedTags := tightExecution.trace.filterMap fun exchange =>
        match exchange.query with
        | .inr ⟨_, .refine (.inl entry)⟩ => some entry.val.start
        | .inr ⟨_, .refine (.inr point)⟩ => some point
        | _ => none
      unless !refinedTags.isEmpty && refinedTags.all (fun point => !oldTags.contains point) &&
          decide ((integralBound tightResult.comparison.left.cells).width < tightAccuracy.tolerance) do
        throw (IO.userError "tighter source request did not reuse the saved point bank")
      let changedRequest : CertifiedProgram.Request := ⟨65, 1, by decide⟩
      let changedInput := Runner.Full.Result.continuation lateInput result changedRequest 1 firstRequest
      let changed := (Runner.Full.computation changedInput).protocol.run (Runner.Full.originalReply changedInput)
      match changed.value with
      | .error _ => throw (IO.userError "changed-stage exponential continuation failed")
      | .ok changedResult =>
          let rebuiltRight := changed.trace.any fun exchange => match exchange.query with
            | .inr ⟨_, .fresh (.right _)⟩ => true
            | .inr ⟨_, .common (.inr _)⟩ => true
            | _ => false
          let builtLeft := changed.trace.any fun exchange => match exchange.query with
            | .inr ⟨_, .fresh (.left _)⟩ => true
            | _ => false
          let oldRightTags := result.comparison.rightFrontier.cells.map fun cell => cell.item.point
          let newRightTags := changedResult.comparison.rightFrontier.cells.map fun cell => cell.item.point
          unless builtLeft && !rebuiltRight && oldRightTags == newRightTags do
            throw (IO.userError "changed-stage continuation rebuilt or lost the retained right source")
          let backInput := Runner.Full.Result.continuation changedInput changedResult lateRequest 1 firstRequest
          let back := (Runner.Full.computation backInput).protocol.run (Runner.Full.originalReply backInput)
          match back.value with
          | .error _ => throw (IO.userError "return to a previously retained exponential stage failed")
          | .ok backResult =>
              unless back.trace.isEmpty && backResult.selected.val.index == 64 do
                throw (IO.userError "return to a previous stage rebuilt its model or source comparison")
              match backResult.progress with
              | .reused _ _ _ _ => pure ()
              | _ => throw (IO.userError "return to a previous stage lost its original source comparison")
  match lateProgram.protocol.replayExact lateExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "out-of-prefix exponential runner did not replay")

/-- Exercise saved and refined source frontiers of the same retained exponential stage. -/
public def run : IO Unit := do
  let fullExecution := fullProgram.protocol.run fullOracle
  match fullExecution.value with
  | .error _ => throw (IO.userError "combined original exponential runner and sources failed")
  | .ok result =>
      let returnedModels := fullExecution.trace.filterMap fun entry =>
        match entry.query, entry.reply with
        | .inl index, .inl receipt => some (index, receipt.model.sample)
        | _, _ => none
      let logicalModels := result.recorded.trace.map fun entry => (entry.query, entry.reply.sample)
      unless !returnedModels.isEmpty && returnedModels.all (fun model => logicalModels.contains model) do
        throw (IO.userError "combined exponential execution lost a returned model from its logical trace")
      unless result.comparison.leftAnchor.stage.sample == result.recorded.observation.selected.sample &&
          !result.recorded.trace.isEmpty && !result.comparison.common.val.readings.isEmpty do
        throw (IO.userError "combined exponential execution lost its recorded selection or common readings")
      let leftBound := integralBound result.comparison.left.cells
      let rightBound := integralBound result.comparison.rightFrontier.cells
      unless decide (Fraction.abs (result.recorded.observation.selected.sample.re -
          result.comparison.rightAnchor.stage.sample.re) ≤
            leftBound.width + rightBound.width + result.comparison.common.val.pointBudget) do
        throw (IO.userError "combined exponential comparison lost its actual point budget")
  match fullProgram.protocol.replayExact fullExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "combined exponential runner and source trace did not replay")

  let wrongIndexOracle (question : Runner.Full.Question fullInput) : Runner.Full.Reply fullInput :=
    match question with
    | .inl index => .inl (Runner.Model.originalReply firstRetained (index + 1))
    | _ => fullOracle question
  let wrongIndex := fullProgram.protocol.run wrongIndexOracle
  match wrongIndex.value with
  | .error (.model (.index requested receipt bank _)) =>
      unless receipt.index == requested + 1 && bank.isEmpty && wrongIndex.trace.length == 1 do
        throw (IO.userError "combined exponential runner lost its wrong model index")
  | _ => throw (IO.userError "combined exponential runner accepted a wrong model index")
  let wrongSourceOracle (question : Runner.Full.Question fullInput) : Runner.Full.Reply fullInput :=
    match question with
    | .inr _ => .inl (Runner.Model.originalReply firstRetained 0)
    | _ => fullOracle question
  let wrongSource := fullProgram.protocol.run wrongSourceOracle
  match wrongSource.value with
  | .error (.sourceOperation completed recorded _) =>
      let logicalIndices := recorded.trace.map fun exchange => exchange.query
      let ordered := match wrongSource.trace.reverse with
        | last :: earlier =>
            let sourceLast := match last.query, last.reply with
              | .inr _, .inl _ => true
              | _, _ => false
            let modelEarlier := earlier.all fun exchange => match exchange.query with
              | .inl index => logicalIndices.contains index
              | .inr _ => false
            sourceLast && modelEarlier
        | [] => false
      unless !recorded.trace.isEmpty && !completed.bank.isEmpty && ordered do
        throw (IO.userError "combined exponential source failure lost its bank, model log or source order")
  | _ => throw (IO.userError "combined exponential runner accepted a wrong source operation")
  let pairedProgram := Runner.Paired.computation fullInput
  let pairedExecution := pairedProgram.protocol.run fullOracle
  let numericalPoint := NumericalPoint.observe Real.source ⟨0, 1⟩ 0 (by decide) (by decide)
    (Real.source 0).initial firstRequest
  have numericalUnit : 0 ≤ numericalPoint.point ∧ numericalPoint.point ≤ 1 := by decide
  let numericalPair ← match ((Paired.attach numericalPoint numericalUnit).protocol.run original).value with
    | .error _ => throw (IO.userError "paired numerical exponential source attachment failed")
    | .ok value => pure value
  match pairedExecution.value with
  | .error impossible => nomatch impossible
  | .ok (original, points) =>
      match original.value with
      | .error _ => throw (IO.userError "paired exponential runner lost the original successful result")
      | .ok _ => pure ()
      unless !points.isEmpty do
        throw (IO.userError "paired exponential runner lost its returned source points")
      let mut leftFound := false
      let mut rightFound := false
      let mut leftCompared := false
      let mut rightCompared := false
      for pair in points do
        match pair.1 with
        | ⟨selectedReceipt, .inl point⟩ =>
            leftFound := true
            unless pair.2.val.re == point.reading && pair.2.val.im == 0 do
              throw (IO.userError "paired exponential left source lost its actual cached reading")
            if point.point == numericalPoint.point then
              unless decide (Norm.Basic.normSq (pair.2.val - numericalPair.paired.midpoint) ≤
                  (numericalPair.paired.real.interval.width +
                    Real.tailRadius (Runner.Full.selectedRequest fullInput selectedReceipt).selection.depth) ^ 2 +
                      (numericalPair.paired.imaginary.interval.width * (1 / 2)) ^ 2) do
                throw (IO.userError "selected exponential sample exceeded its same-tag numerical bound")
              leftCompared := true
        | ⟨_, .inr point⟩ =>
            rightFound := true
            unless pair.2.val.re == point.reading && pair.2.val.im == 0 do
              throw (IO.userError "paired exponential right source lost its actual cached reading")
            if point.point == numericalPoint.point then
              unless decide (Norm.Basic.normSq (pair.2.val - numericalPair.paired.midpoint) ≤
                  (numericalPair.paired.real.interval.width + Real.tailRadius fullInput.right.selection.depth) ^ 2 +
                    (numericalPair.paired.imaginary.interval.width * (1 / 2)) ^ 2) do
                throw (IO.userError "independent exponential sample exceeded its same-tag numerical bound")
              rightCompared := true
      unless leftFound && rightFound && leftCompared && rightCompared do
        throw (IO.userError "paired exponential runner lost a source owner")
  match pairedProgram.protocol.replayExact pairedExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "paired exponential runner did not replay")
  let pairedWrong := pairedProgram.protocol.run wrongSourceOracle
  match pairedWrong.value with
  | .ok (original, _) =>
      match original.value with
      | .error (.sourceOperation _ recorded _) =>
          unless !recorded.trace.isEmpty do
            throw (IO.userError "paired source failure lost the original model trace")
      | _ => throw (IO.userError "paired runner did not preserve the original wrong-source failure")
  | .error impossible => nomatch impossible
  checkLateStages
  let modelExecution := modelObservation.protocol.run modelOracle
  match modelExecution.value with
  | .error _ => throw (IO.userError "original exponential model receipt was rejected")
  | .ok verified =>
      let logical := verified.execution.val.trace.map fun entry => (entry.query, entry.reply.model.sample)
      let displayed := modelExecution.trace.filterMap fun entry =>
        entry.reply.map fun receipt => (entry.query, receipt.model.sample)
      unless !displayed.isEmpty && displayed.all (fun model => logical.contains model) do
        throw (IO.userError "exponential model lowering lost an actual returned model")
      match verified.execution.val.value with
      | .ok observation =>
          unless observation.selected.sample == runnerPrepared.observation.selected.sample do
            throw (IO.userError "exponential model lowering changed the selected integration sample")
      | .error _ => throw (IO.userError "original exponential model execution failed")
  match modelObservation.protocol.replayExact modelExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "exponential model receipts did not replay")
  let badModel := modelObservation.protocol.run fun index =>
    some (Runner.Model.originalReply firstRetained (index + 1))
  match badModel.value with
  | .error (.index requested receipt bank _) =>
      unless receipt.index == requested + 1 && bank.isEmpty && badModel.trace.length == 1 do
        throw (IO.userError "wrong exponential model index did not retain its actual failure")
  | _ => throw (IO.userError "wrong exponential model index was accepted")
  let runnerExecution := runnerComparison.protocol.run runnerOracle
  match runnerExecution.value with
  | .error _ => throw (IO.userError "original exponential integration comparison rejected its source replies")
  | .ok compared =>
      unless compared.leftStage.stage.sample == runnerPrepared.observation.selected.sample &&
          !runnerPrepared.trace.isEmpty && !compared.common.val.readings.isEmpty do
        throw (IO.userError "exponential integration comparison lost its recorded stage or common readings")
      let selected := Runner.stageRequest runnerPrepared firstRequest
      let leftBound := integralBound (StageComparison.retainedFrontier selected compared.leftStage).cells
      let rightBound := integralBound (StageComparison.retainedFrontier secondStageRequest compared.rightStage).cells
      unless decide (Fraction.abs (runnerPrepared.observation.selected.sample.re -
          compared.rightStage.stage.sample.re) ≤
            leftBound.width + rightBound.width + compared.common.val.pointBudget) do
        throw (IO.userError "returned common readings did not pay for the integration sample comparison")
  match runnerComparison.protocol.replayExact runnerExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "exponential integration comparison did not replay its source observations")
  let comparedExecution := stageComparison.protocol.run stageOracle
  match comparedExecution.value with
  | .error _ => throw (IO.userError "original exponential stage comparison rejected its source replies")
  | .ok compared =>
      let sameStages : Bool :=
        compared.leftStage.stage.sample == firstStageRequest.stage.sample &&
          compared.leftStage.stage.sample == first.stage.sample &&
          compared.rightStage.stage.sample == second.stage.sample && !compared.common.val.readings.isEmpty
      unless sameStages do
        throw (IO.userError "exponential stage comparison lost its actual retained stages or common readings")
  match stageComparison.protocol.replayExact comparedExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "exponential stage comparison did not replay its source observations")
  let wrongPoint := SourcePoint.observe secondStageRequest.source ⟨0, 0⟩ 0 le_rfl le_rfl
  let wrongOracle (question : StageComparison.Question firstStageRequest secondStageRequest) :
      StageComparison.Reply firstStageRequest secondStageRequest :=
    match question with
    | .left _ => .right wrongPoint
    | _ => stageOracle question
  let invalid := stageComparison.protocol.run wrongOracle
  match invalid.value with
  | .error (.operation (.left _)) =>
      unless invalid.trace.length == 1 do
        throw (IO.userError "wrong exponential stage operation did not stop at its original request")
  | _ => throw (IO.userError "wrong exponential stage operation was accepted")
  let wrongTag := SourcePoint.observe firstStageRequest.source ⟨-1, -1⟩ (-1) le_rfl le_rfl
  let wrongTagOracle (question : StageComparison.Question firstStageRequest secondStageRequest) :
      StageComparison.Reply firstStageRequest secondStageRequest :=
    match question with
    | .left _ => .left wrongTag
    | _ => stageOracle question
  let invalidTag := stageComparison.protocol.run wrongTagOracle
  match invalidTag.value with
  | .error (.left _) =>
      unless invalidTag.trace.length == 1 do
        throw (IO.userError "wrong exponential source tag did not stop at its original request")
  | _ => throw (IO.userError "wrong exponential source tag was accepted")
  let previous := first.sourceResult.frontier
  let savedProgram := Source.Observation.continuation first previous [] firstRequest
  let savedOracle := SourceFrontier.Continuous.Observation.Continuation.originalReplyAll
    (Source.Observation.preparation firstPolicy firstSchedule 0 firstRequest)
  unless (savedProgram.protocol.run savedOracle).trace.isEmpty do
    throw (IO.userError "sufficient exponential frontier made a source request")
  match first.advanceFrontier previous [] firstRequest with
  | .reused _ _ => pure ()
  | .refined _ _ _ _ _ _ => throw (IO.userError "sufficient exponential frontier was rebuilt")
  let tighter : AccuracyRequest := ⟨1, by decide⟩
  let observed := Source.Observation.continuation first previous [] tighter
  let oracle := SourceFrontier.Continuous.Observation.Continuation.originalReplyAll
    (Source.Observation.preparation firstPolicy firstSchedule 0 tighter)
  let execution := observed.protocol.run oracle
  if execution.trace.isEmpty then
    throw (IO.userError "tighter exponential request did not exercise a source observation")
  let next ← match execution.value with
  | .error _ => throw (IO.userError "original exponential source replies were rejected")
  | .ok result =>
      unless decide ((integralBound result.frontier.cells).width < tighter.tolerance) do
        throw (IO.userError "observed exponential continuation missed its request")
      pure result
  match observed.protocol.replayExact execution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "exponential continuation did not replay its source observations")
  match next with
  | .reused _ _ => throw (IO.userError "exponential refinement did not exercise its retained point bank")
  | .refined _ cached _ _ _ _ =>
      let available := SourceFrontier.Producer.effectiveBank previous cached
      unless cached.isEmpty && available.map (fun point => point.point) ==
          previous.cells.map (fun cell => cell.item.point) do
        throw (IO.userError "exponential refinement lost the saved source points")
  unless decide ((integralBound next.frontier.cells).width < tighter.tolerance) do
    throw (IO.userError "continued exponential frontier did not meet its request")
  match first.advanceFrontier next.frontier [] firstRequest with
  | .reused _ _ => pure ()
  | .refined _ _ _ _ _ _ => throw (IO.userError "continued exponential frontier was not reused")

end TestPurelib.Integration.Exponential.Program.Source
