module
import TestPurelib.Integration.Exponential.Program.Source
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Exponential.Program.Source.Numerical
import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical
import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Paired
import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Retry
import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.HistoryRetry
import Purelib.Integration.Exponential.Real

/-! Mixed numerical exponential integration and interrupted continuation regressions. -/

namespace TestPurelib.Integration.Exponential.Program.Source.Numerical

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
open Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query.Program
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

/-- An independently computed numerical exponential frontier. -/
private def numerical := Purelib.Integration.Exponential.Real.integrate firstRequest

/-- The common point request retains a separate positive uncertainty budget. -/
private def pointRequest : AccuracyRequest := ⟨2, by decide⟩

/-- The initial numerical history's accuracy request. -/
private def mixedNumericalRequest : AccuracyRequest := ⟨1 / 4, by decide⟩
/-- The original production and independent numerical histories for mixed comparison. -/
private def mixedInput : Runner.Numerical.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0 :=
  ⟨fullInput, Purelib.Integration.Exponential.Real.integrationProcess.initial, mixedNumericalRequest, pointRequest,
    [], []⟩
/-- The original mixed production and numerical comparison program. -/
private def mixedProgram := Runner.Numerical.computation mixedInput
/-- Original replies for the mixed comparison program. -/
private def mixedOracle := Runner.Numerical.originalReply mixedInput

example := Runner.Numerical.computation_original mixedInput
example := Runner.Numerical.computation_replay mixedInput mixedOracle
example (result : Runner.Numerical.Result mixedInput) := result.recorded_difference_le_actual
example (result : Runner.Numerical.Result mixedInput) := result.pointBudget_le
example (input : Runner.Numerical.Paired.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0)
    (result : Runner.Numerical.Result input.mixed) (entry : Runner.Numerical.Paired.CommonCompleted input result) :=
  Runner.Numerical.Paired.CommonCompleted.sample_midpoint_normSq_le input result entry
example (input : Runner.Numerical.Paired.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0)
    (result : Runner.Numerical.Result input.mixed) (entry : Runner.Numerical.Paired.CommonCompleted input result) :=
  Runner.Numerical.Paired.CommonCompleted.finite_reading input result entry


example : Fraction.abs (first.stage.sample.re - numerical.answer) ≤
    (integralBound first.sourceResult.frontier.cells).width + (integralBound numerical.frontier.cells).width +
      (pointRequest.tolerance + Real.tailRadius (Selection.selection firstPolicy firstSchedule 0).depth) :=
  Program.Source.sample_answer_difference_le first numerical.frontier numerical.answer numerical.answer_contains
    pointRequest

example : (Program.Source.numericalCommon first numerical.frontier pointRequest).pointBudget ≤
    pointRequest.tolerance + Real.tailRadius (Selection.selection firstPolicy firstSchedule 0).depth :=
  Program.Source.numerical_pointBudget_le first numerical.frontier pointRequest

/-- Tighter requests for mixed point and numerical-mesh continuation. -/
private def tighterPoint : AccuracyRequest :=
  ⟨1 / ((100 : Nat) : Fraction.Rational), Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Cast.Order.natCast_pos_direct (n := 100) (by decide))⟩
/-- A tighter numerical integration history request. -/
private def tighterNumerical : AccuracyRequest := ⟨1 / 8, by decide⟩

/-- Repeat the mixed comparison using its actual returned banks. -/
private def checkMixedRepeat (mixedResult : Runner.Numerical.Result mixedInput) : IO Unit := do
  let resumedMixedInput := Runner.Numerical.Result.continuation mixedInput mixedResult
    runnerRequest 2 firstRequest mixedNumericalRequest pointRequest
  let resumedMixed := (Runner.Numerical.computation resumedMixedInput).protocol.run
    (Runner.Numerical.originalReply resumedMixedInput)
  match resumedMixed.value with
  | .error _ => throw (IO.userError "mixed exponential continuation failed")
  | .ok result =>
      unless resumedMixed.trace.isEmpty && !result.common.readings.isEmpty &&
          decide (mixedResult.leftBank.length ≤ result.leftBank.length) &&
          decide (mixedResult.rightBank.length ≤ result.rightBank.length) do
        throw (IO.userError "adequate mixed continuation did not reuse both returned point banks")

/-- Refine the mixed point request using the returned banks. -/
private def checkMixedTighterPoints (mixedResult : Runner.Numerical.Result mixedInput) : IO Unit := do
  let tighterMixedInput := Runner.Numerical.Result.continuation mixedInput mixedResult
    runnerRequest 2 firstRequest mixedNumericalRequest tighterPoint
  let tighterMixed := (Runner.Numerical.computation tighterMixedInput).protocol.run
    (Runner.Numerical.originalReply tighterMixedInput)
  match tighterMixed.value with
  | .error _ => throw (IO.userError "tighter mixed point continuation failed")
  | .ok result =>
      unless !tighterMixed.trace.isEmpty && !result.common.readings.isEmpty &&
          decide (mixedResult.leftBank.length ≤ result.leftBank.length) &&
          decide (mixedResult.rightBank.length ≤ result.rightBank.length) do
        throw (IO.userError "tighter mixed continuation lost its supplied point banks")

/-- Refine the numerical mesh while retaining the original common banks. -/
private def checkMixedMesh (mixedResult : Runner.Numerical.Result mixedInput) : IO Unit := do
  let changedMixedInput := Runner.Numerical.Result.continuation mixedInput mixedResult
    runnerRequest 2 firstRequest tighterNumerical pointRequest
  let changedMixed := (Runner.Numerical.computation changedMixedInput).protocol.run
    (Runner.Numerical.originalReply changedMixedInput)
  match changedMixed.value with
  | .error _ => throw (IO.userError "mixed continuation with a tighter numerical mesh failed")
  | .ok result =>
      unless decide (mixedResult.numerical.state.1.cells.length < result.numerical.state.1.cells.length) &&
          decide (mixedResult.leftBank.length ≤ result.leftBank.length) &&
          decide (mixedResult.rightBank.length ≤ result.rightBank.length) do
        throw (IO.userError "changed numerical mesh lost its earlier common point banks")

/-- Retain completed common points and resume after a later wrong operation. -/
private def checkMixedFailure (mixedResult : Runner.Numerical.Result mixedInput) : IO Unit := do
  let secondTag ← match mixedResult.common.readings with
    | _ :: second :: _ => pure second.tag
    | _ => throw (IO.userError "mixed comparison did not produce two common occurrences")
  let wrongMixedOracle (question : Runner.Numerical.Question mixedInput) : Runner.Numerical.Reply mixedInput :=
    match question with
    | .inr (.inr (_, .inl point)) =>
        if point == secondTag then .inl (.inl (Runner.Model.originalReply firstRetained 0))
        else mixedOracle question
    | _ => mixedOracle question
  let rejectedMixed := mixedProgram.protocol.run wrongMixedOracle
  match rejectedMixed.value with
  | .error failure =>
      match failure with
      | .common production numerical _ failed _ leftBank _ rightBank _ =>
          unless !production.recorded.trace.isEmpty && !numerical.execution.trace.isEmpty &&
              !failed.completed.val.isEmpty && !leftBank.isEmpty && !rightBank.isEmpty do
            throw (IO.userError "mixed source failure lost its completed points or original owners")
          match Runner.Numerical.Failure.continuation mixedInput failure
              runnerRequest 2 firstRequest mixedNumericalRequest pointRequest with
          | none => throw (IO.userError "mixed source failure did not retain its continuation")
          | some retryInput =>
              let retry := (Runner.Numerical.computation retryInput).protocol.run
                (Runner.Numerical.originalReply retryInput)
              let completedTags := failed.completed.val.map fun reading => reading.tag
              let repeated := retry.trace.any fun exchange => match exchange.query with
                | .inr (.inr (_, .inl point)) => completedTags.contains point
                | .inr (.inr (_, .inr (point, _))) => completedTags.contains point.val
                | _ => false
              match retry.value with
              | .ok result =>
                  unless !result.common.readings.isEmpty && !repeated &&
                      decide (leftBank.length ≤ result.leftBank.length) &&
                      decide (rightBank.length ≤ result.rightBank.length) do
                    throw (IO.userError "mixed retry lost the partial returned point banks")
              | .error _ => throw (IO.userError "mixed retry after a wrong source operation failed")
      | _ => throw (IO.userError "mixed exponential observer returned the wrong failure")
  | _ => throw (IO.userError "mixed exponential observer accepted a wrong common-point operation")

/-- A wrong ball after a returned refinement retains and resumes that exact Gaussian state. -/
private def checkMixedPendingBall (mixedResult : Runner.Numerical.Result mixedInput) : IO Unit := do
  let input := Runner.Numerical.Result.continuation mixedInput mixedResult
    runnerRequest 2 firstRequest mixedNumericalRequest tighterPoint
  let program := Runner.Numerical.computation input
  let complete := program.protocol.run (Runner.Numerical.originalReply input)
  let result ← match complete.value with
    | .ok result => pure result
    | .error _ => throw (IO.userError "tighter mixed point run failed")
  let secondTag ← match result.common.readings with
    | _ :: second :: _ => pure second.tag
    | _ => throw (IO.userError "tighter mixed point run did not return two occurrences")
  let before := complete.trace.takeWhile fun exchange => match exchange.query with
    | .inr (.inr (_, .inr (point, .ball _))) => point.val != secondTag
    | _ => true
  let target ← match complete.trace.drop before.length with
    | exchange :: _ => pure exchange.query
    | _ => throw (IO.userError "second mixed point did not request its Gaussian ball")
  let state ← match target with
    | .inr (.inr (_, .inr (_, .ball state))) => pure state
    | _ => throw (IO.userError "wrong target in mixed ball test")
  let hadRefinement := before.any fun exchange => match exchange.query with
    | .inr (.inr (_, .inr (point, .refine _ _ _))) => point.val == secondTag
    | _ => false
  unless hadRefinement do
    throw (IO.userError "mixed ball test did not first return the original refinement")
  let failedTrace := before ++ [⟨target, .inl (.inl (Runner.Model.originalReply firstRetained 0))⟩]
  match program.protocol.replayExact failedTrace with
  | .ok (.error failure) =>
      match failure with
      | .common _ _ _ stopped _ _ _ _ _ =>
          match stopped.reason.reason with
          | .pending _ receipt =>
              unless receipt.next.val == state && !stopped.completed.val.isEmpty do
                throw (IO.userError "mixed failure lost its earlier points or exact returned refinement")
              match Runner.Numerical.Retry.ofFailure input failure with
              | none => throw (IO.userError "mixed pending ball lost its retry owner")
              | some retryOwner =>
                  let retryProgram := Runner.Numerical.Retry.computation input retryOwner
                  let retry := retryProgram.protocol.run (Runner.Numerical.originalReply input)
                  let repeatedRefinement := retry.trace.any fun exchange => match exchange.query with
                    | .inr (.inr (_, .inr (point, .refine _ _ _))) => point.val == secondTag
                    | _ => false
                  let firstIsBall := match retry.trace with
                    | first :: _ => decide (first.query = target)
                    | [] => false
                  unless firstIsBall && !repeatedRefinement do
                    throw (IO.userError "pending mixed retry repeated the saved refinement")
                  match retry.value with
                  | .error impossible => nomatch impossible
                  | .ok resumed => match resumed.value with
                    | .completed _ _ common _ =>
                        unless common.readings.length == result.common.readings.length do
                          throw (IO.userError "pending mixed retry lost its certified common prefix or suffix")
                    | _ => throw (IO.userError "pending mixed retry did not complete the common batch")
          | _ => throw (IO.userError "mixed wrong ball did not retain a pending refinement")
      | _ => throw (IO.userError "mixed wrong ball returned the wrong outer failure")
  | _ => throw (IO.userError "mixed wrong ball replay did not fail")

/-- Retry a failed numerical refinement without rerunning the completed production or history prefix. -/
private def checkMixedRefinementStop : IO Unit := do
  let execution := mixedProgram.protocol.run mixedOracle
  let original ← match execution.value with
    | .ok result => pure result
    | .error _ => throw (IO.userError "original mixed numerical history failed")
  let queries := execution.trace.filterMap fun exchange => match exchange.query with
    | .inr (.inl question) => some question
    | _ => none
  let refinement ← match queries with
    | first :: _ :: next :: _ =>
        match next.2 with
        | .refine _ _ _ =>
            if first.1.val != next.1.val then pure next
            else throw (IO.userError "mixed refinement test did not reach a second point")
        | _ => throw (IO.userError "mixed refinement test did not reach a refinement")
    | _ => throw (IO.userError "mixed refinement test did not complete an earlier point")
  let before := execution.trace.takeWhile fun exchange => match exchange.query with
    | .inr (.inl question) => decide (question ≠ refinement)
    | _ => true
  let target : Runner.Numerical.Question mixedInput := .inr (.inl refinement)
  let failedTrace := before ++ [⟨target, .inl (.inl (Runner.Model.originalReply firstRetained 0))⟩]
  let failure ← match mixedProgram.protocol.replayExact failedTrace with
    | .ok (.error failure) => pure failure
    | _ => throw (IO.userError "mixed numerical history accepted a wrong refinement")
  let stopped ← match failure with
    | .numericalStop production _ stopped _ =>
        unless !production.recorded.trace.isEmpty && !stopped.before.isEmpty do
          throw (IO.userError "mixed refinement failure lost its production or completed prefix")
        match stopped.reason with
        | .initial _ => pure stopped
        | .pending _ => throw (IO.userError "mixed refinement failure invented a returned state")
    | _ => throw (IO.userError "mixed refinement failure changed its owner")
  let owner ← match HistoryRetry.ofFailure mixedInput failure with
    | some owner => pure owner
    | none => throw (IO.userError "mixed refinement failure lost its retry owner")
  let reject (question : Runner.Numerical.Question mixedInput) : Runner.Numerical.Reply mixedInput :=
    if question = target then .inl (.inl (Runner.Model.originalReply firstRetained 0)) else mixedOracle question
  let failedAgain := (HistoryRetry.computationProgress mixedInput owner).protocol.run reject
  let failedAgainValue ← match failedAgain.value.result with
    | .error failure => pure failure
    | .ok _ => throw (IO.userError "mixed history accepted a second wrong refinement")
  match failedAgainValue with
  | .numericalStop production _ later _ =>
      unless !production.recorded.trace.isEmpty &&
          decide (later.before.map (fun exchange => exchange.query) =
            stopped.before.map (fun exchange => exchange.query)) do
        throw (IO.userError "repeated mixed refinement lost the earlier prefix")
      match later.reason with
      | .initial _ => pure ()
      | .pending _ => throw (IO.userError "repeated mixed refinement invented a returned state")
  | _ => throw (IO.userError "repeated mixed refinement changed its failure owner")
  unless failedAgain.trace.length == 1 &&
      decide (failedAgain.trace.map (fun exchange => exchange.query) = [target]) do
    throw (IO.userError "repeated mixed refinement changed its original query")
  let ownerAgain ← match HistoryRetry.Outcome.next mixedInput failedAgain.value with
    | some owner => pure owner
    | none => throw (IO.userError "repeated mixed refinement lost its retry owner")
  let initialTagged := failedTrace.filterMap fun exchange => match exchange.query with
    | .inr (.inl _) => some exchange.query
    | _ => none
  match ownerAgain.earlier with
  | [earlier] =>
      unless decide (earlier.trace.map (fun exchange => exchange.query) = initialTagged) &&
          decide (ownerAgain.execution.trace.map (fun exchange => exchange.query) = [target]) do
        throw (IO.userError "mixed refinement retry lost its actual tagged attempts")
  | _ => throw (IO.userError "mixed refinement retry changed its attempt history")
  let retry := (HistoryRetry.computationProgress mixedInput ownerAgain).protocol.run mixedOracle
  let repeatedProduction := retry.trace.any fun exchange => match exchange.query with
    | .inl _ => true
    | _ => false
  match retry.value.result with
  | .error _ => throw (IO.userError "mixed refinement retry did not finish")
  | .ok result =>
      unless !repeatedProduction && !result.common.readings.isEmpty &&
          decide (result.numerical.execution.trace.map (fun exchange => exchange.query) =
            original.numerical.execution.trace.map (fun exchange => exchange.query)) &&
          (integralBound result.numerical.state.1.cells).lower ==
            (integralBound original.numerical.state.1.cells).lower &&
          (integralBound result.numerical.state.1.cells).upper ==
            (integralBound original.numerical.state.1.cells).upper do
        throw (IO.userError "mixed refinement retry changed the original history or answer")

/-- Retain an interrupted numerical history at the actual mixed-runner boundary. -/
private def checkMixedNumericalStop : IO Unit := do
  let execution := mixedProgram.protocol.run mixedOracle
  let original ← match execution.value with
    | .ok result => pure result
    | .error _ => throw (IO.userError "original mixed numerical history failed")
  let queries := execution.trace.filterMap fun exchange => match exchange.query with
    | .inr (.inl question) => some question
    | _ => none
  let (first, refinement, ball) ← match queries with
    | first :: _ :: refinement :: ball :: _ => pure (first, refinement, ball)
    | _ => throw (IO.userError "mixed numerical history did not request two Gaussian points")
  let state ← match refinement.2, ball.2 with
    | .refine _ _ _, .ball state =>
        if refinement.1.val == ball.1.val && first.1.val != ball.1.val then pure state
        else throw (IO.userError "mixed numerical refinement and ball have different tags")
    | _, _ => throw (IO.userError "mixed numerical history changed its original request order")
  let before := execution.trace.takeWhile fun exchange => match exchange.query with
    | .inr (.inl question) => decide (question ≠ ball)
    | _ => true
  let target : Runner.Numerical.Question mixedInput := .inr (.inl ball)
  let failedTrace := before ++ [⟨target, .inl (.inl (Runner.Model.originalReply firstRetained 0))⟩]
  let failure ← match mixedProgram.protocol.replayExact failedTrace with
    | .ok (.error failure) => pure failure
    | _ => throw (IO.userError "mixed numerical wrong ball did not retain its original history")
  let stopped ← match failure with
    | .numericalStop production _ stopped _ =>
        unless !production.recorded.trace.isEmpty && !stopped.before.isEmpty do
          throw (IO.userError "mixed numerical failure lost the production owner or completed history")
        pure stopped
    | _ => throw (IO.userError "mixed numerical wrong ball returned a different failure")
  match stopped.reason with
  | .initial _ => throw (IO.userError "mixed numerical failure lost its returned refinement")
  | .pending receipt =>
      unless receipt.refined.val == state do
        throw (IO.userError "mixed numerical failure changed its returned Gaussian state")
  let retryOwner ← match HistoryRetry.ofFailure mixedInput failure with
    | some owner => pure owner
    | none => throw (IO.userError "mixed numerical failure lost its retry owner")
  let rejectBall (question : Runner.Numerical.Question mixedInput) : Runner.Numerical.Reply mixedInput :=
    if question = target then .inl (.inl (Runner.Model.originalReply firstRetained 0)) else mixedOracle question
  let failedAgain := (HistoryRetry.computationProgress mixedInput retryOwner).protocol.run rejectBall
  let failedAgainValue ← match failedAgain.value.result with
    | .error failure => pure failure
    | .ok _ => throw (IO.userError "mixed numerical retry accepted a second wrong ball")
  match failedAgainValue with
  | .numericalStop production _ later _ =>
      unless !production.recorded.trace.isEmpty &&
          decide (later.before.map (fun exchange => exchange.query) =
            stopped.before.map (fun exchange => exchange.query)) do
        throw (IO.userError "repeated mixed ball failure lost its production or numerical prefix")
      match later.reason with
      | .pending receipt => unless receipt.refined.val == state do
          throw (IO.userError "repeated mixed ball failure changed its returned refinement")
      | .initial _ => throw (IO.userError "repeated mixed ball failure lost its returned refinement")
  | _ => throw (IO.userError "repeated mixed ball failure changed its failure owner")
  unless failedAgain.trace.length == 1 &&
      decide (failedAgain.trace.map (fun exchange => exchange.query) = [target]) do
    throw (IO.userError "repeated mixed ball failure repeated the refinement")
  let retryOwnerAgain ← match HistoryRetry.Outcome.next mixedInput failedAgain.value with
    | some owner => pure owner
    | none => throw (IO.userError "repeated mixed ball failure lost its retry owner")
  let initialTagged := failedTrace.filterMap fun exchange => match exchange.query with
    | .inr (.inl _) => some exchange.query
    | _ => none
  match retryOwnerAgain.earlier with
  | [earlier] =>
      unless decide (earlier.trace.map (fun exchange => exchange.query) = initialTagged) &&
          decide (retryOwnerAgain.execution.trace.map (fun exchange => exchange.query) = [target]) do
        throw (IO.userError "mixed ball retry lost its actual tagged attempts")
  | _ => throw (IO.userError "mixed ball retry changed its attempt history")
  let retryProgram := HistoryRetry.computationProgress mixedInput retryOwnerAgain
  let retry := retryProgram.protocol.run mixedOracle
  let firstIsBall := match retry.trace with
    | first :: _ => decide (first.query = target)
    | [] => false
  let repeated := retry.trace.any fun exchange => match exchange.query with
    | .inr (.inl question) => decide (question = refinement)
    | _ => false
  unless firstIsBall && !repeated do
    throw (IO.userError "mixed numerical retry repeated its returned refinement")
  let repeatedProduction := retry.trace.any fun exchange => match exchange.query with
    | .inl _ => true
    | _ => false
  match retry.value.result with
  | .error _ => throw (IO.userError "mixed numerical retry did not finish")
  | .ok result =>
      unless !repeatedProduction && !result.common.readings.isEmpty &&
          decide (result.numerical.execution.trace.map (fun exchange => exchange.query) =
            original.numerical.execution.trace.map (fun exchange => exchange.query)) &&
          (integralBound result.numerical.state.1.cells).lower ==
            (integralBound original.numerical.state.1.cells).lower &&
          (integralBound result.numerical.state.1.cells).upper ==
            (integralBound original.numerical.state.1.cells).upper &&
          result.common.readings.map (fun reading => reading.tag) ==
            original.common.readings.map (fun reading => reading.tag) do
        throw (IO.userError "mixed numerical retry lost its source owners or requested accuracy")
  match retryProgram.protocol.replayExact retry.trace with
  | .ok replayed =>
      unless replayed.previous.earlier.length == 1 do
        throw (IO.userError "mixed retry replay lost its earlier tagged attempt")
      match replayed.result with
      | .error _ => throw (IO.userError "mixed retry replay changed its successful outcome")
      | .ok result =>
          unless !result.common.readings.isEmpty &&
              (integralBound result.numerical.state.1.cells).lower ==
                (integralBound original.numerical.state.1.cells).lower &&
              (integralBound result.numerical.state.1.cells).upper ==
                (integralBound original.numerical.state.1.cells).upper do
            throw (IO.userError "mixed retry replay changed the actual comparison")
  | .error _ => throw (IO.userError "mixed retry trace failed exact replay")

/-- A retry that reaches a later failed question retains the enlarged original prefix. -/
private def checkMixedLaterStop : IO Unit := do
  let original := mixedProgram.protocol.run mixedOracle
  let questions := original.trace.filterMap fun exchange => match exchange.query with
    | .inr (.inl question) => some question
    | _ => none
  let (first, later) ← match questions with
    | first :: _ :: later :: _ =>
        match first.2, later.2 with
        | .refine _ _ _, .refine _ _ _ =>
            if first.1.val != later.1.val then pure (first, later)
            else throw (IO.userError "later-stop fixture did not reach a distinct point")
        | _, _ => throw (IO.userError "later-stop fixture did not reach two refinements")
    | _ => throw (IO.userError "later-stop fixture did not reach two numerical points")
  let firstTarget : Runner.Numerical.Question mixedInput := .inr (.inl first)
  let laterTarget : Runner.Numerical.Question mixedInput := .inr (.inl later)
  let rejectFirst (question : Runner.Numerical.Question mixedInput) : Runner.Numerical.Reply mixedInput :=
    if question = firstTarget then .inl (.inl (Runner.Model.originalReply firstRetained 0)) else mixedOracle question
  let failed := mixedProgram.protocol.run rejectFirst
  let initial ← match failed.value with
    | .error (.numericalStop _ _ stopped _) => pure stopped
    | _ => throw (IO.userError "later-stop fixture did not fail its first numerical query")
  let owner ← match failed.value with
    | .error failure => match HistoryRetry.ofFailure mixedInput failure with
      | some retryOwner => pure retryOwner
      | none => throw (IO.userError "later-stop fixture lost the first retry owner")
    | .ok _ => throw (IO.userError "later-stop fixture accepted its first bad reply")
  let rejectLater (question : Runner.Numerical.Question mixedInput) : Runner.Numerical.Reply mixedInput :=
    if question = laterTarget then .inl (.inl (Runner.Model.originalReply firstRetained 0)) else mixedOracle question
  let second := (HistoryRetry.computationProgress mixedInput owner).protocol.run rejectLater
  let stopped ← match second.value.result with
    | .error (.numericalStop _ _ stopped _) => pure stopped
    | _ => throw (IO.userError "retry did not stop at its later numerical query")
  unless decide (stopped.question ≠ initial.question) && decide (initial.before.length < stopped.before.length) &&
      second.trace.any (fun exchange => decide (exchange.query = firstTarget)) &&
      second.trace.any (fun exchange => decide (exchange.query = laterTarget)) do
    throw (IO.userError "later stop lost the newly completed original prefix")
  let next ← match HistoryRetry.Outcome.next mixedInput second.value with
    | some retryOwner => pure retryOwner
    | none => throw (IO.userError "later stop did not retain its retry owner")
  unless next.earlier.length == 1 &&
      decide (next.execution.trace.map (fun exchange => exchange.query) =
        second.value.execution.trace.map (fun exchange => exchange.query)) do
    throw (IO.userError "later stop lost its ordered tagged attempts")
  let finished := (HistoryRetry.computationProgress mixedInput next).protocol.run mixedOracle
  match original.value, finished.value.result with
  | .ok expected, .ok actual =>
      unless decide (actual.numerical.execution.trace.map (fun exchange => exchange.query) =
          expected.numerical.execution.trace.map (fun exchange => exchange.query)) &&
          (integralBound actual.numerical.state.1.cells).lower ==
            (integralBound expected.numerical.state.1.cells).lower &&
          (integralBound actual.numerical.state.1.cells).upper ==
            (integralBound expected.numerical.state.1.cells).upper do
        throw (IO.userError "later-stop retry changed the original history or integral bounds")
  | _, _ => throw (IO.userError "later-stop retry did not reach the final comparison")

/-- A later common failure retains every earlier tagged history and common attempt. -/
private def checkMixedHistoryCommonHandoff : IO Unit := do
  let input := { mixedInput with pointRequest := tighterPoint }
  let program := Runner.Numerical.computation input
  let oracle := Runner.Numerical.originalReply input
  let original := program.protocol.run oracle
  let first ← match original.trace.find? (fun exchange => match exchange.query with
      | .inr (.inl (_, .refine _ _ _)) => true
      | _ => false) with
    | some exchange => pure exchange.query
    | none => throw (IO.userError "history/common fixture did not request a numerical refinement")
  let commonBall ← match original.trace.find? (fun exchange => match exchange.query with
      | .inr (.inr (_, .inr (_, .ball _))) => true
      | _ => false) with
    | some exchange => pure exchange.query
    | none => throw (IO.userError "history/common fixture did not request a common Gaussian ball")
  let wrong : Runner.Numerical.Reply input := .inl (.inl (Runner.Model.originalReply firstRetained 0))
  let rejectFirst (question : Runner.Numerical.Question input) : Runner.Numerical.Reply input :=
    if question = first then wrong else oracle question
  let initial := program.protocol.run rejectFirst
  let owner ← match initial.value with
    | .error failure => match HistoryRetry.ofFailure input failure with
      | some retryOwner => pure retryOwner
      | none => throw (IO.userError "history/common fixture lost its stopped numerical owner")
    | .ok _ => throw (IO.userError "history/common fixture accepted its first bad reply")
  let rejectBall (question : Runner.Numerical.Question input) : Runner.Numerical.Reply input :=
    if question = commonBall then wrong else oracle question
  let history := (HistoryRetry.computationProgress input owner).protocol.run rejectBall
  match history.value.result with
  | .error (.common _ _ _ stopped _ _ _ _ _) =>
      match stopped.reason.reason with
      | .pending _ _ => pure ()
      | _ => throw (IO.userError "history/common fixture lost the returned common refinement")
  | _ => throw (IO.userError "history retry did not reach the expected common failure")
  let commonOwner ← match HistoryRetry.CommonRequest.ofExecution input history with
    | some retryOwner => pure retryOwner
    | none => throw (IO.userError "common failure lost its preceding history outcome")
  unless decide (commonOwner.history.value.previous.execution.trace.map (fun exchange => exchange.query) =
      owner.execution.trace.map (fun exchange => exchange.query)) &&
      decide (commonOwner.history.value.execution.trace.map (fun exchange => exchange.query) =
        history.value.execution.trace.map (fun exchange => exchange.query)) &&
      decide (commonOwner.history.trace.map (fun exchange => exchange.query) =
        history.trace.map (fun exchange => exchange.query)) do
    throw (IO.userError "common retry lost its original tagged history attempts")
  match commonOwner.history.trace.find? (fun exchange => decide (exchange.query = commonBall)) with
  | some exchange => match exchange.reply with
    | .inl (.inl _) => pure ()
    | _ => throw (IO.userError "common handoff lost the actual wrong outer reply")
  | none => throw (IO.userError "common handoff lost the failed tagged request")
  let firstCommon := (HistoryRetry.commonComputation input commonOwner).protocol.run rejectBall
  match firstCommon.value.execution.value with
  | .error impossible => nomatch impossible
  | .ok execution => match execution.value with
    | .pending _ => pure ()
    | _ => throw (IO.userError "common retry did not retain the repeated ball failure")
  let next ← match HistoryRetry.CommonOutcome.next input firstCommon.value with
    | some retryOwner => pure retryOwner
    | none => throw (IO.userError "repeated common failure lost its retry owner")
  unless next.earlier.length == 1 &&
      decide (next.history.value.execution.trace.map (fun exchange => exchange.query) =
        history.value.execution.trace.map (fun exchange => exchange.query)) do
    throw (IO.userError "repeated common retry lost earlier history or common work")
  match next.earlier with
  | [⟨_, execution⟩] =>
      match execution.trace with
      | [exchange] => match exchange.reply with
        | .inl (.inl _) => pure ()
        | _ => throw (IO.userError "repeated common retry changed its wrong outer reply")
      | _ => throw (IO.userError "repeated common retry changed its tagged attempt")
  | _ => throw (IO.userError "repeated common retry lost its ordered tagged attempt")
  let finalProgram := HistoryRetry.commonComputation input next
  let final := finalProgram.protocol.run oracle
  match final.value.execution.value with
  | .error impossible => nomatch impossible
  | .ok execution => match execution.value with
    | .completed _ _ common _ =>
        let production := next.current.production
        let numerical := next.current.numerical
        let leftBound := integralBound production.comparison.left.cells
        let rightBound := integralBound numerical.state.1.cells
        unless decide (Fraction.abs (production.recorded.observation.selected.sample.re - rightBound.midpoint) ≤
            leftBound.width + rightBound.width + common.pointBudget) &&
            decide (common.pointBudget ≤ tighterPoint.tolerance +
              Real.tailRadius production.comparison.receipt.selection.depth) do
          throw (IO.userError "resumed common readings did not pay for the integral comparison")
    | _ => throw (IO.userError "common handoff did not finish the original batch")
  match finalProgram.protocol.replayExact final.trace with
  | .ok replayed => unless replayed.previous.earlier.length == 1 do
      throw (IO.userError "common retry replay lost its earlier actual attempt")
  | .error _ => throw (IO.userError "common handoff trace did not replay")

/-- Paired continuation keeps the actual mixed comparison and both ordered paired stages. -/
private def checkMixedPaired : IO Unit := do
  let pairedInput : Runner.Numerical.Paired.Input firstPolicy secondPolicy firstSchedule secondSchedule 0 0 :=
    ⟨mixedInput, tighterPoint, [], none⟩
  let program := Runner.Numerical.Paired.computation pairedInput
  let execution := program.protocol.run (Runner.Numerical.originalReply mixedInput)
  match execution.value with
  | .common mixed result _ frontier common =>
      unless !mixed.trace.isEmpty && !result.common.readings.isEmpty &&
          !frontier.value.completed.isEmpty && frontier.value.pending.isEmpty && frontier.value.failure.isNone &&
          !common.value.completed.isEmpty && common.value.pending.isEmpty && common.value.failure.isNone do
        throw (IO.userError "paired mixed run lost its returned comparison or completed points")
      match program.protocol.replayExact execution.trace with
      | .ok (.common _ _ _ _ _) => pure ()
      | _ => throw (IO.userError "paired mixed execution did not replay")
      match Runner.Numerical.Paired.Outcome.continuation pairedInput execution.value
          runnerRequest 2 firstRequest mixedNumericalRequest pointRequest tighterPoint with
      | none => throw (IO.userError "paired mixed execution lost its continuation")
      | some next =>
          let repeated := (Runner.Numerical.Paired.computation next).protocol.run
            (Runner.Numerical.originalReply next.mixed)
          match repeated.value with
          | .common _ _ _ repeatedFrontier repeatedCommon =>
              unless repeated.trace.isEmpty && repeatedFrontier.value.failure.isNone &&
                  repeatedCommon.value.failure.isNone do
                throw (IO.userError "adequate paired continuation did not reuse the returned pair bank")
          | _ => throw (IO.userError "adequate paired continuation did not complete")
      let secondTag ← match frontier.value.completed with
        | _ :: second :: _ => pure second.occurrence.val.item.point
        | _ => throw (IO.userError "paired mixed frontier did not contain two occurrences")
      let before := frontier.trace.takeWhile fun exchange => match exchange.query with
        | .inr (.inl (point, .refine _ _ _)) => point.val != secondTag
        | _ => true
      let target ← match frontier.trace.drop before.length with
        | exchange :: _ => pure exchange.query
        | _ => throw (IO.userError "second paired point did not request an imaginary refinement")
      let failedTrace := mixed.trace ++ before ++
        [⟨target, .inl (.inl (Runner.Model.originalReply firstRetained 0))⟩]
      match program.protocol.replayExact failedTrace with
      | .ok (.frontier _ _ _ failed) =>
          match failed.value.failure with
          | some (.operation _) =>
              unless !failed.value.completed.isEmpty && !failed.value.pending.isEmpty &&
                  decide (failed.value.completed.length < failed.value.bank.length) do
                throw (IO.userError "paired failure lost its completed or partially attached state")
          | _ => throw (IO.userError "paired failure did not retain the wrong outer operation")
      | _ => throw (IO.userError "paired replay did not stop at the wrong outer operation")
      -- `before` ends immediately before the second point's imaginary refinement.
      let afterRefinement := frontier.trace.drop before.length
      let refinement ← match afterRefinement with
        | exchange :: _ => pure exchange
        | [] => throw (IO.userError "paired second point did not refine its imaginary coordinate")
      let afterFirst := afterRefinement.drop 1
      let beforeBall := afterFirst.takeWhile fun exchange => match exchange.query with
        | .inr (.inl (point, .ball _)) => point.val != secondTag
        | _ => true
      let ball ← match afterFirst.drop beforeBall.length with
        | exchange :: _ => pure exchange.query
        | _ => throw (IO.userError "paired second point did not read its refined Gaussian ball")
      let ballState ← match ball with
        | .inr (.inl (_, .ball state)) => pure state
        | _ => throw (IO.userError "paired ball test selected a different operation")
      let ballFailureTrace := mixed.trace ++ before ++ [refinement] ++ beforeBall ++
        [⟨ball, .inl (.inl (Runner.Model.originalReply firstRetained 0))⟩]
      match program.protocol.replayExact ballFailureTrace with
      | .ok failedOutcome =>
          match failedOutcome with
          | .frontier _ _ _ failed =>
              match failed.value.failure with
              | some (.pending receipt (.operation _)) =>
                  unless receipt.next.val == ballState &&
                      !failed.value.completed.isEmpty && !failed.value.pending.isEmpty do
                    throw (IO.userError "paired ball failure lost its completed and pending occurrences")
                  match Runner.Numerical.Paired.Outcome.continuation pairedInput failedOutcome
                      runnerRequest 2 firstRequest mixedNumericalRequest pointRequest tighterPoint with
                  | none => throw (IO.userError "paired ball failure lost its pending refinement")
                  | some next =>
                      let retry := (Runner.Numerical.Paired.computation next).protocol.run
                        (Runner.Numerical.originalReply next.mixed)
                      let firstIsBall := match retry.trace with
                        | first :: _ => match first.query with
                            | .inr (.inl (point, .ball state)) => point.val == secondTag && state == ballState
                            | _ => false
                        | [] => false
                      let repeated := retry.trace.any fun exchange => match exchange.query with
                        | .inr (.inl (point, .refine _ _ _)) => point.val == secondTag
                        | _ => false
                      unless firstIsBall && !repeated do
                        throw (IO.userError "paired ball retry repeated its returned imaginary refinement")
                      match retry.value with
                      | .common _ _ _ first second =>
                          unless first.value.failure.isNone && second.value.failure.isNone do
                            throw (IO.userError "paired ball retry retained a failure")
                      | _ => throw (IO.userError "paired ball retry did not finish")
              | _ => throw (IO.userError "paired ball failure lost its wrong outer operation")
          | _ => throw (IO.userError "paired ball failure stopped outside its original frontier")
      | _ => throw (IO.userError "paired ball failure trace did not replay")
  | _ => throw (IO.userError "paired mixed execution did not complete")

/-- Exercise production, numerical histories, retries and their common comparison. -/
public def run : IO Unit := do
  let mixedExecution := mixedProgram.protocol.run mixedOracle
  let mixedResult ← match mixedExecution.value with
    | .error _ => throw (IO.userError "combined production and numerical exponential observation failed")
    | .ok result => pure result
  unless !mixedResult.production.recorded.trace.isEmpty && !mixedResult.common.readings.isEmpty do
    throw (IO.userError "mixed exponential comparison lost its actual original owners or common readings")
  let exactBound := integralBound mixedResult.production.comparison.left.cells
  let numericalBound := integralBound mixedResult.numerical.state.1.cells
  unless decide (Fraction.abs (mixedResult.production.recorded.observation.selected.sample.re -
      numericalBound.midpoint) ≤ exactBound.width + numericalBound.width + mixedResult.common.pointBudget) do
    throw (IO.userError "returned common readings did not pay for the mixed integration comparison")
  unless decide (mixedResult.common.pointBudget ≤ pointRequest.tolerance +
      Real.tailRadius mixedResult.production.comparison.receipt.selection.depth) do
    throw (IO.userError "mixed exponential common budget exceeded its selected finite-tail bound")
  match mixedProgram.protocol.replayExact mixedExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "mixed exponential production/numerical trace did not replay")
  checkMixedRepeat mixedResult
  checkMixedTighterPoints mixedResult
  checkMixedMesh mixedResult
  checkMixedFailure mixedResult
  checkMixedPendingBall mixedResult
  checkMixedRefinementStop
  checkMixedNumericalStop
  checkMixedLaterStop
  checkMixedHistoryCommonHandoff
  checkMixedPaired

end TestPurelib.Integration.Exponential.Program.Source.Numerical
