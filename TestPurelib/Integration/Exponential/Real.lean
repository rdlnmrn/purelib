module
import Purelib.Integration.Exponential.Real
import Purelib.Integration.Exponential.Real.Observation
import Purelib.Integration.Exponential.Real.Observation.Progress
import Purelib.Integration.Exponential.Real.Paired.Frontier
import Purelib.Integration.Exponential.Real.Paired.History
import Purelib.Integration.Cell.Numerical.Continuous.Observation
import Purelib.Integration.Cell.Numerical.Continuous.Observation.Continuation
import Purelib.Approximation.Gaussian.Exponential.Horner.Real.State

/-! Integration of actual finite exponential point processes on the rational unit interval. -/

namespace TestPurelib.Integration.Exponential.Real

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Integration
open Purelib.Integration.Exponential.Real
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.Exponential.Real.Observation
open Purelib.Computation.Query

/-- Two finite requests with independent computed source frontiers. -/
private def firstRequest : AccuracyRequest := ⟨8, by decide⟩
private def secondRequest : AccuracyRequest := ⟨4, by decide⟩
private def first := integrate firstRequest
private def second := integrate secondRequest

/-- The actual preparation and its original finite point-query computation. -/
private def prepared := first.preparation
private def observation := Observation.computation prepared
private def originalReply := Observation.originalReply prepared

/-- A fallback that makes an additional actual request if it is ever called. -/
private def changedReply (_ : Unit) (entry : Observation.Entry prepared) :=
  (originalReply entry).refine ⟨1, by decide⟩

example : (integralBound first.frontier.cells).width < firstRequest.tolerance := first.accurate

example : (integralBound second.frontier.cells).width < secondRequest.tolerance := second.accurate

/-- A nonempty actual integration history and a later refinement. -/
private def process := integrationProcess
private def saved := process.request process.initial firstRequest.tolerance firstRequest.positive
private def later := process.request saved secondRequest.tolerance secondRequest.positive

/-- The original exponential integration history has an executable point-state observer and replay. -/
example := Observation.Continuation.historyComputation_original Real.modulus saved secondRequest

example := Observation.Continuation.historyComputation_replay Real.modulus saved secondRequest

/-- An actual exponential point state and its paired original Gaussian coordinate state. -/
private def pointState := (Real.source (1 / 2)).request (Real.source (1 / 2)).initial 2 (by decide)
private def otherPointState := (Real.source (1 / 2)).request (Real.source (1 / 2)).initial 1 (by decide)
private theorem pointUnit : 0 ≤ (1 / 2 : Purelib.Data.Rat.Fraction.Rational) ∧
    (1 / 2 : Purelib.Data.Rat.Fraction.Rational) ≤ 1 := ⟨by decide, by decide⟩
private def pairedPoint := Real.pairedState (1 / 2) pointUnit pointState

/-- The same actual point state observed through its tagged Gaussian source operations. -/
private def taggedPoint : Point := ⟨1 / 2, pointUnit⟩
private def gaussianPrevious := Real.originalState (1 / 2) pointUnit pointState

example := coordinate_original taggedPoint gaussianPrevious firstRequest

example := coordinate_replay taggedPoint gaussianPrevious firstRequest

/-- A first observation and the two actual cache decisions at its original rational tag. -/
private def retainedPoint := NumericalPoint.observe Real.source ⟨0, 1⟩ (1 / 2) (by decide) (by decide)
  (Real.source (1 / 2)).initial firstRequest
private def cachedSelection := NumericalPoint.selectBank Real.source [retainedPoint] (1 / 2) firstRequest
private def freshSelection := NumericalPoint.selectBank Real.source [] (1 / 2) firstRequest

example := selection_original taggedPoint firstRequest cachedSelection

example := selection_replay taggedPoint firstRequest freshSelection

example : ((selection taggedPoint firstRequest cachedSelection).protocol.run original).trace.length = 0 := by
  decide +kernel

example : ((selection taggedPoint firstRequest freshSelection).protocol.run original).trace.length = 2 := by
  decide +kernel

/-- The actual retained integration request is lowered through the tagged Gaussian operations. -/
example := history_original saved secondRequest

example := history_replay saved secondRequest

example (state : integrationProcess.State)
    (adequate : (integralBound state.1.cells).width < firstRequest.tolerance) :
    ((history state firstRequest).protocol.run original).trace = [] :=
  history_reused state firstRequest adequate original

example : pairedPoint.real.interval = (Real.source (1 / 2)).bound pointState :=
  Real.pairedState_real_bound (1 / 2) pointUnit pointState

example : pairedPoint.real.interval.Contains ((Real.approximation (1 / 2) pointUnit).sample pairedPoint.current).re ∧
    pairedPoint.imaginary.interval.Contains ((Real.approximation (1 / 2) pointUnit).sample pairedPoint.current).im :=
  Real.pairedState_sample_inside (1 / 2) pointUnit pointState pairedPoint.current (Nat.le_refl _)

example : Purelib.Data.Gaussian.Norm.Basic.normSq
    (pairedPoint.midpoint - (Real.pairedState (1 / 2) pointUnit otherPointState).midpoint) ≤
      (pairedPoint.real.interval.width + (Real.pairedState (1 / 2) pointUnit otherPointState).real.interval.width) ^ 2 +
        (pairedPoint.imaginary.interval.width +
          (Real.pairedState (1 / 2) pointUnit otherPointState).imaginary.interval.width) ^ 2 :=
  Real.pairedState_midpoints_normSq_le (1 / 2) pointUnit pointState otherPointState

example : IntegrationFrontierRefines (process.frontier later) (process.frontier saved) :=
  process.request_refines saved secondRequest.tolerance secondRequest.positive

example : (Real.source 0).Coherent := Real.modulus.coherent 0 (by decide) (by decide)

example : (observation.protocol.run originalReply).value.map
    (Observation.cachedCell prepared) = prepared.frontier.cells :=
  Observation.original_cells prepared

example : (observation.protocol.replayExact (observation.protocol.run originalReply).trace).map
    (List.map (Observation.cachedCell prepared)) = .ok prepared.frontier.cells :=
  Observation.replay_cells prepared

example : observation.protocol.run (Boundary.Trace.overlay (observation.protocol.run originalReply).trace
      (changedReply ())) = observation.protocol.run originalReply :=
  Observation.payload_erasure prepared () changedReply

example : (observation.protocol.run originalReply).trace.length = 3 := by decide +kernel

/-- The actual selected source predecessor, or no request for an adequate retained point. -/
private def selectedPredecessor (point : Point) (request : AccuracyRequest)
    (bank : List (NumericalPoint Real.source)) : Option Nat :=
  match NumericalPoint.selectBank Real.source bank point.val request with
  | .reuse _ _ _ => none
  | .request previous => some (Real.originalState point.val point.property previous).current

/-- Check real integration's saved history, exact source-call accounting, replay and rejected replies. -/
public def run : IO Unit := do
  let demand : AccuracyRequest := ⟨1 / 4, by decide⟩
  let program := history saved demand
  let execution := program.protocol.run original
  let outer ← match execution.value with
    | .error _ => throw (IO.userError "original tagged Gaussian source reply was rejected")
    | .ok result => pure result
  let continued ← match outer.value with
    | .error _ => throw (IO.userError "original numerical integration reply was rejected")
    | .ok state => pure state
  unless decide ((integralBound continued.1.cells).width < demand.tolerance) do
    throw (IO.userError "continued exponential frontier missed its width request")
  if outer.trace.isEmpty then
    throw (IO.userError "tighter saved exponential request made no point requests")
  let producer := NumericalFrontier.Continuous.producer Real.modulus
  let bank := NumericalFrontier.Producer.effectiveBank saved.1 (producer.retainedReadings saved.2)
  let prepared := NumericalFrontier.Continuous.Preparation.prepare Real.modulus demand
  let mut inner := execution.trace
  for exchange in outer.trace do
    let (point, predecessor) := match exchange.query with
      | .inl entry =>
          let point := preparedPoint prepared entry
          (point, selectedPredecessor point prepared.pointRequest bank)
      | .inr (bank, child) =>
          let point := commonPoint child
          (point, selectedPredecessor point demand bank)
    match predecessor with
    | none => pure ()
    | some expected =>
      match inner with
      | first :: second :: tail =>
          unless first.query.1.val == point.val && second.query.1.val == point.val &&
              first.reply.1.val == point.val && second.reply.1.val == point.val do
            throw (IO.userError "tagged Gaussian requests lost the original numerical point")
          match first.query.2, second.query.2 with
          | .refine previous target _, .ball after =>
              unless previous == expected do
                throw (IO.userError "Gaussian refinement discarded the actual selected predecessor")
              match first.reply.2, second.reply.2 with
              | ⟨.refine returnedPrevious returnedTarget _, returned⟩, ⟨.ball ballState, _⟩ =>
                  unless returnedPrevious == previous && returnedTarget == target &&
                      returned.val == after && ballState == after do
                    throw (IO.userError "ball readback did not use the same returned Gaussian state")
              | _, _ => throw (IO.userError "Gaussian replies changed the original operations")
          | _, _ => throw (IO.userError "numerical point did not refine and then read its Gaussian ball")
          inner := tail
      | _ => throw (IO.userError "missing tagged Gaussian requests")
  unless inner.isEmpty do throw (IO.userError "extra tagged Gaussian request was recorded")
  let replayed ← match program.protocol.replayExact execution.trace with
    | .ok (.ok result) => pure result
    | _ => throw (IO.userError "tagged Gaussian source trace failed exact replay")
  let replayedState ← match replayed.value with
    | .ok state => pure state
    | .error _ => throw (IO.userError "replay changed the original numerical result")
  unless replayed.trace.length == outer.trace.length &&
      (integralBound replayedState.1.cells).lower == (integralBound continued.1.cells).lower &&
      (integralBound replayedState.1.cells).upper == (integralBound continued.1.cells).upper do
    throw (IO.userError "replay changed retained point occurrences or the integral enclosure")
  unless ((history continued demand).protocol.run original).trace.isEmpty do
    throw (IO.userError "satisfied saved exponential request made a Gaussian call")
  unless ((selection taggedPoint firstRequest cachedSelection).protocol.run original).trace.isEmpty do
    throw (IO.userError "sufficient cached exponential point made a Gaussian call")
  let wrongOperation : Query → Reply := fun question =>
    ⟨question.1, Purelib.Approximation.Gaussian.Process.Coordinate.Observation.original
      (Observation.process question.1) (.ball (0 : Nat))⟩
  let invalidOperation := program.protocol.run wrongOperation
  unless invalidOperation.trace.length == 1 do
    throw (IO.userError "wrong Gaussian operation did not stop at its first request")
  match invalidOperation.value with
  | .error (.operation _ invalid) =>
      match invalid.requested with
      | .refine _ _ _ => pure ()
      | .ball _ => throw (IO.userError "wrong-operation failure lost its original request")
  | _ => throw (IO.userError "wrong Gaussian operation was not reported")
  let firstTag ← match execution.trace with
    | first :: _ => pure first.query.1
    | [] => throw (IO.userError "Gaussian trace was unexpectedly empty")
  let other : Point := if firstTag.val == 0 then ⟨1, ⟨by decide, by decide⟩⟩ else ⟨0, ⟨by decide, by decide⟩⟩
  let wrongPoint : Query → Reply := fun _ =>
    ⟨other, Purelib.Approximation.Gaussian.Process.Coordinate.Observation.original
      (Observation.process other) (.ball (0 : Nat))⟩
  let invalidPoint := program.protocol.run wrongPoint
  unless invalidPoint.trace.length == 1 do
    throw (IO.userError "wrong Gaussian point did not stop at its first request")
  match invalidPoint.value with
  | .error (.point requested reported _) =>
      unless requested.val == firstTag.val && reported.val == other.val do
        throw (IO.userError "wrong-point failure lost the actual rational owners")
  | _ => throw (IO.userError "wrong Gaussian point was not reported")

  let progressProgram := Progress.history saved demand
  let wrongPointProgress := progressProgram.protocol.run wrongPoint
  let wrongPointStop ← match wrongPointProgress.value with
    | .error stopped => pure stopped
    | .ok _ => throw (IO.userError "progress history accepted a wrong Gaussian point")
  match wrongPointStop.reason with
  | .initial (.point requested reported _) =>
      unless requested.val == firstTag.val && reported.val == other.val && wrongPointStop.before.isEmpty do
        throw (IO.userError "progress history lost the wrong-point failure or its original prefix")
  | _ => throw (IO.userError "progress history changed the wrong-point failure")
  let afterWrongPoint := (Progress.resumeHistory saved demand wrongPointStop).protocol.run original
  match afterWrongPoint.value with
  | .error _ => throw (IO.userError "wrong-point retry did not finish")
  | .ok result =>
      unless decide (result.trace.map (fun exchange => exchange.query) =
          outer.trace.map (fun exchange => exchange.query)) do
        throw (IO.userError "wrong-point retry changed the original numerical request order")
      match result.value with
      | .error _ => throw (IO.userError "wrong-point retry returned a numerical error")
      | .ok resumed =>
          unless (integralBound resumed.1.cells).lower == (integralBound continued.1.cells).lower &&
              (integralBound resumed.1.cells).upper == (integralBound continued.1.cells).upper do
            throw (IO.userError "wrong-point retry changed the original integration answer")
  -- After one completed point, retain the next point's successful refinement
  -- when its original Gaussian ball reply identifies the wrong state.
  let progressExecution := progressProgram.protocol.run original
  let tracePrefix := progressExecution.trace.take 3
  let target ← match progressExecution.trace.drop 3 with
    | exchange :: _ => pure exchange.query
    | _ => throw (IO.userError "real history did not issue two refinement/ball pairs")
  let state ← match target.2 with
    | .ball state => pure state
    | _ => throw (IO.userError "real history did not read the second returned ball")
  let refinement ← match tracePrefix with
  | [first, second, third] =>
      match first.query.2, second.query.2, third.query.2, third.reply.2 with
      | .refine _ _ _, .ball _, .refine _ _ _, ⟨.refine _ _ _, returned⟩ =>
          unless first.query.1.val == second.query.1.val && first.query.1.val != target.1.val &&
              third.query.1.val == target.1.val && returned.val == state do
            throw (IO.userError "real history did not retain the second point's returned refinement")
          pure third.query
      | _, _, _, _ => throw (IO.userError "real history changed its ordered Gaussian pairs")
  | _ => throw (IO.userError "real history did not complete the earlier point")
  let wrong : Reply := ⟨target.1, Purelib.Approximation.Gaussian.Process.Coordinate.Observation.original
    (Observation.process target.1) (.ball (state + 1))⟩
  let wrongRefinement : Reply := ⟨refinement.1, Purelib.Approximation.Gaussian.Process.Coordinate.Observation.original
    (Observation.process refinement.1) (.ball (0 : Nat))⟩
  let failedRefinementTrace := tracePrefix.take 2 ++ [⟨refinement, wrongRefinement⟩]
  let initialStop ← match progressProgram.protocol.replayExact failedRefinementTrace with
    | .ok (.error stopped) => pure stopped
    | _ => throw (IO.userError "real history did not stop at the wrong refinement")
  match initialStop.reason with
  | .initial _ => unless !initialStop.before.isEmpty do
      throw (IO.userError "failed refinement lost the earlier completed point")
  | .pending _ => throw (IO.userError "failed refinement invented a returned state")
  let rejectRefinement (question : Query) : Reply :=
    if question = refinement then wrongRefinement else original question
  let progressedFailure := (Progress.resumeHistory saved demand wrongPointStop).protocol.run rejectRefinement
  let progressedStop ← match progressedFailure.value with
    | .error stopped => pure stopped
    | .ok _ => throw (IO.userError "history retry did not stop at its later original question")
  unless progressedStop.before.length > wrongPointStop.before.length &&
      decide (progressedStop.before.map (fun exchange => exchange.query) =
        initialStop.before.map (fun exchange => exchange.query)) &&
      decide (progressedFailure.trace.map (fun exchange => exchange.query) =
        failedRefinementTrace.map (fun exchange => exchange.query)) do
    throw (IO.userError "later history failure lost its newly completed prefix")
  let progressedRetry := (Progress.resumeHistory saved demand progressedStop).protocol.run original
  unless decide (progressedRetry.trace.map (fun exchange => exchange.query) =
      (progressExecution.trace.drop 2).map (fun exchange => exchange.query)) do
    throw (IO.userError "later history retry repeated the earlier completed point")
  match progressedRetry.value with
  | .error _ => throw (IO.userError "later history retry did not finish")
  | .ok result =>
      unless decide (result.trace.map (fun exchange => exchange.query) =
          outer.trace.map (fun exchange => exchange.query)) do
        throw (IO.userError "later history retry changed the original numerical request order")
      match result.value with
      | .error _ => throw (IO.userError "later history retry returned a numerical error")
      | .ok resumed =>
          unless (integralBound resumed.1.cells).lower == (integralBound continued.1.cells).lower &&
              (integralBound resumed.1.cells).upper == (integralBound continued.1.cells).upper do
            throw (IO.userError "later history retry changed the original integration answer")
  let failedAgain := (Progress.resumeHistory saved demand initialStop).protocol.run rejectRefinement
  let repeatedInitial ← match failedAgain.value with
    | .error stopped => pure stopped
    | .ok _ => throw (IO.userError "real history accepted the repeated wrong refinement")
  match repeatedInitial.reason with
  | .initial _ => pure ()
  | .pending _ => throw (IO.userError "repeated wrong refinement invented a returned state")
  unless failedAgain.trace.length == 1 &&
      decide (failedAgain.trace.map (fun exchange => exchange.query) = [refinement]) &&
      decide (repeatedInitial.before.map (fun exchange => exchange.query) =
        initialStop.before.map (fun exchange => exchange.query)) do
    throw (IO.userError "repeated refinement failure lost its original request or prefix")
  let afterInitial := (Progress.resumeHistory saved demand repeatedInitial).protocol.run original
  match afterInitial.value with
  | .error _ => throw (IO.userError "retry after a wrong refinement failed")
  | .ok result =>
      unless decide (result.trace.map (fun exchange => exchange.query) =
          outer.trace.map (fun exchange => exchange.query)) do
        throw (IO.userError "refinement retry changed the original numerical request order")
      match result.value with
      | .error _ => throw (IO.userError "refinement retry returned a numerical error")
      | .ok resumed =>
          unless (integralBound resumed.1.cells).lower == (integralBound continued.1.cells).lower &&
              (integralBound resumed.1.cells).upper == (integralBound continued.1.cells).upper do
            throw (IO.userError "refinement retry changed the original integration answer")
  let failedTrace := tracePrefix ++ [⟨target, wrong⟩]
  let stopped ← match progressProgram.protocol.replayExact failedTrace with
    | .ok (.error stopped) => pure stopped
    | _ => throw (IO.userError "real history did not stop at the wrong ball")
  match stopped.reason with
  | .initial _ => throw (IO.userError "real history lost its returned Gaussian refinement")
  | .pending receipt =>
      unless receipt.refined.val == state && !stopped.before.isEmpty do
        throw (IO.userError "real history lost its completed prefix or returned refinement")
  let rejectBall (question : Query) : Reply := if question = target then wrong else original question
  let failedBallAgain := (Progress.resumeHistory saved demand stopped).protocol.run rejectBall
  let repeatedBall ← match failedBallAgain.value with
    | .error stopped => pure stopped
    | .ok _ => throw (IO.userError "real history accepted the repeated wrong ball")
  match repeatedBall.reason with
  | .initial _ => throw (IO.userError "repeated ball failure lost its returned refinement")
  | .pending receipt =>
      unless receipt.refined.val == state do
        throw (IO.userError "repeated ball failure changed its returned refinement")
  unless failedBallAgain.trace.length == 1 &&
      decide (failedBallAgain.trace.map (fun exchange => exchange.query) = [target]) &&
      decide (repeatedBall.before.map (fun exchange => exchange.query) =
        stopped.before.map (fun exchange => exchange.query)) do
    throw (IO.userError "repeated ball failure lost its original request or prefix")
  let retryProgram := Progress.resumeHistory saved demand repeatedBall
  let retry := retryProgram.protocol.run original
  let firstIsBall := match retry.trace with
    | first :: _ => decide (first.query = target)
    | [] => false
  let repeated := retry.trace.any fun exchange => decide (exchange.query = refinement)
  unless firstIsBall && !repeated do
    throw (IO.userError "real history retry repeated the retained refinement")
  match retry.value with
  | .error _ => throw (IO.userError "real history retry did not finish")
  | .ok result =>
      unless decide (result.trace.map (fun exchange => exchange.query) =
          outer.trace.map (fun exchange => exchange.query)) do
        throw (IO.userError "ball retry changed the original numerical request order")
      match result.value with
      | .error _ => throw (IO.userError "resumed numerical integration returned an error")
      | .ok resumed =>
          unless (integralBound resumed.1.cells).lower == (integralBound continued.1.cells).lower &&
              (integralBound resumed.1.cells).upper == (integralBound continued.1.cells).upper do
            throw (IO.userError "ball retry changed the original integration answer")
  match retryProgram.protocol.replayExact retry.trace with
  | .ok (.ok replayed) =>
      unless decide (replayed.trace.map (fun exchange => exchange.query) =
          outer.trace.map (fun exchange => exchange.query)) do
        throw (IO.userError "ball retry replay changed the original numerical request order")
      match replayed.value with
      | .error _ => throw (IO.userError "ball retry replay returned a numerical error")
      | .ok resumed =>
          unless (integralBound resumed.1.cells).lower == (integralBound continued.1.cells).lower &&
              (integralBound resumed.1.cells).upper == (integralBound continued.1.cells).upper do
            throw (IO.userError "ball retry replay changed the original integration answer")
  | _ => throw (IO.userError "ball retry trace failed exact replay")

/-- A finer real point request for the changed-state cache regression. -/
private def finePointRequest : AccuracyRequest := ⟨1 / 4, by decide⟩

/-- A failed imaginary request retains its already observed origin ball for a later continuation. -/
public def runPaired : IO Unit := do
  let request : AccuracyRequest := ⟨1 / 16, by decide⟩
  let failRefinement : Query → Reply := fun question =>
    match question.2 with
    | .ball _ => original question
    | .refine _ _ _ =>
        ⟨question.1, Purelib.Approximation.Gaussian.Process.Coordinate.Observation.original
          (Observation.process question.1) (.ball (0 : Nat))⟩
  let failed := (Paired.Frontier.observeFrontier
    first.frontier request []).protocol.run failRefinement
  unless failed.trace.length == 2 do
    throw (IO.userError "paired frontier failure did not retain the origin and failed refinement calls")
  match failed.value.failure with
  | some (.operation _ _) => pure ()
  | _ => throw (IO.userError "paired frontier did not retain the typed imaginary failure")
  unless failed.value.completed.isEmpty && failed.value.pending.length == first.frontier.cells.length do
    throw (IO.userError "paired frontier failure lost its pending original occurrences")
  let saved ← match failed.value.bank with
    | [saved] => pure saved
    | _ => throw (IO.userError "paired frontier failure discarded its attached origin ball")
  let continued := (Paired.Frontier.observe saved.owner saved.unit
    failed.value.bank request).protocol.run original
  unless continued.trace.length == 2 do
    throw (IO.userError "paired continuation reread the retained origin ball")
  match continued.trace with
  | firstCall :: secondCall :: [] =>
      match firstCall.query.2, secondCall.query.2 with
      | .refine _ _ _, .ball _ => pure ()
      | _, _ => throw (IO.userError "paired continuation did not refine and read the returned ball")
  | _ => throw (IO.userError "paired continuation lost its actual Gaussian calls")
  match continued.value with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "paired continuation rejected the original source")
  let changed : NumericalPoint Real.source := NumericalPoint.refine saved.owner finePointRequest
  let previousGaussian := Real.originalState saved.owner.point saved.unit saved.owner.state
  let changedGaussian := Real.originalState changed.point saved.unit changed.state
  unless previousGaussian.current != changedGaussian.current do
    throw (IO.userError "changed-state regression did not refine the original real source state")
  let changedExecution := (Paired.Frontier.observe changed saved.unit
    failed.value.bank request).protocol.run original
  match changedExecution.trace with
  | firstCall :: secondCall :: [] =>
      match firstCall.query.2, secondCall.query.2 with
      | .refine _ _ _, .ball _ => pure ()
      | _, _ => throw (IO.userError "changed real state did not reuse its saved origin ball")
  | _ => throw (IO.userError "changed real state repeated an origin read or lost its imaginary requests")
  match changedExecution.value with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "changed real state rejected the original Gaussian source")

/-- Observe a nonempty saved integration history and replay its paired frontier. -/
public def runPairedHistory : IO Unit := do
  let imaginary : AccuracyRequest := ⟨1 / 2, by decide⟩
  let program := Paired.History.observe saved firstRequest imaginary []
  let execution := program.protocol.run original
  let result ← match execution.value with
    | .error _ => throw (IO.userError "paired history rejected the original Gaussian source")
    | .ok result => pure result
  match result with
  | .numerical _ _ _ => throw (IO.userError "paired history rejected the original numerical execution")
  | .paired outer next _ progress =>
      unless outer.trace.isEmpty do
        throw (IO.userError "satisfied real history made an extra numerical source request")
      unless progress.failure.isNone && progress.pending.isEmpty &&
          progress.completed.length == next.1.cells.length do
        throw (IO.userError "paired history did not retain every original frontier occurrence")
      unless !execution.trace.isEmpty do
        throw (IO.userError "paired history did not record its original Gaussian requests")
      let replayed := program.protocol.replayExact execution.trace
      match replayed with
      | .error _ => throw (IO.userError "paired history failed exact replay")
      | .ok (.error _) => throw (IO.userError "paired history replay changed a successful source result")
      | .ok (.ok _) => pure ()
      let repeated := (Paired.History.observe
        next firstRequest imaginary progress.bank).protocol.run original
      unless repeated.trace.isEmpty do
        throw (IO.userError "paired history repeated an adequate saved Gaussian observation")

end TestPurelib.Integration.Exponential.Real
