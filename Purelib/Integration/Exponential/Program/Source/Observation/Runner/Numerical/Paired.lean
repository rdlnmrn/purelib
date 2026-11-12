module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical
public import Purelib.Integration.Exponential.Real.Paired.Frontier

/-!
# Paired observations of the returned production and numerical comparison

The actual numerical frontier and the common readings returned by the mixed
runner supply paired Gaussian point observations. The same saved paired bank
is passed through both stages and retains work when an operation fails.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Paired

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.Exponential.Real

set_option genInjectivity false in
/-- A returned imaginary refinement awaiting its original Gaussian ball. -/
structure Pending where
  /-- The complete original numerical point that owns the paired state. -/
  point : NumericalPoint Horner.Real.source
  /-- The original point lies in the unit interval. -/ unit : 0 ≤ point.point ∧ point.point ≤ 1
  /-- The exact paired state used as the imaginary predecessor. -/ saved : Real.Paired.PointState point unit
  /-- The positive imaginary request whose refinement was returned. -/ request : AccuracyRequest
  /-- The exact original Gaussian state returned by that refinement. -/ next :
    Coordinate.Observation.ReturnedState saved.paired.imaginaryAtCurrent request.tolerance request.positive

/-- Select a pending refinement only for the exact point, request and imaginary predecessor. -/
@[expose] def Pending.matching (pending : Option Pending) (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : Real.Paired.PointState point unit)
    (request : AccuracyRequest) :
    Option (Coordinate.Observation.ReturnedState saved.paired.imaginaryAtCurrent request.tolerance request.positive) :=
  match pending with
  | none => none
  | some ⟨oldPoint, oldUnit, oldSaved, oldRequest, next⟩ => by
      if samePoint : oldPoint = point then
        cases samePoint
        if sameRequest : oldRequest = request then
          cases sameRequest
          if sameState : oldSaved.paired.imaginaryAtCurrent = saved.paired.imaginaryAtCurrent then
            exact some (sameState ▸ next)
          else exact none
        else exact none
      else exact none

set_option genInjectivity false in
/-- The original mixed runner, an imaginary request and its actual saved paired bank. -/
structure Input (policy rightPolicy : Geometry.Policy) (schedule rightSchedule : PositiveStride)
    (extraDepth rightExtra : Nat) where
  /-- The original production and numerical request. -/ mixed :
    Numerical.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra
  /-- The requested imaginary-coordinate width. -/ imaginary : AccuracyRequest
  /-- Paired point states retained from earlier original requests. -/ bank : List Real.Paired.Frontier.Saved
  /-- An interrupted original imaginary refinement, when its ball is still pending. -/ pending : Option Pending

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

/-- The original combined production, numerical and Gaussian operation. -/
abbrev Question := Numerical.Question input.mixed

/-- Replies retain the original operation and source owner. -/
abbrev Reply := Numerical.Reply input.mixed

set_option genInjectivity false in
/-- A wrong outer operation or invalid original Gaussian response. -/
inductive PointError where
  /-- A paired Gaussian operation received a reply to another outer operation. -/ | operation
      (question : Real.Observation.Query)
  /-- The Gaussian reply identified an invalid original point or operation. -/ | gaussian
      (failure : Real.Observation.Failure)

set_option genInjectivity false in
/-- The first failed paired operation, optionally retaining a returned imaginary refinement. -/
inductive PointFailure where
  /-- A paired Gaussian operation received a reply to another outer operation. -/ | operation
      (question : Real.Observation.Query)
  /-- The Gaussian reply identified an invalid original point or operation. -/ | gaussian
      (failure : Real.Observation.Failure)
  /-- An imaginary refinement was returned before its ball request failed. -/ | pending
      (receipt : Pending) (reason : PointError)

/-- Convert the original point-operation error without inventing a pending refinement. -/
@[expose] def PointError.toFailure : PointError → PointFailure
  | .operation question => .operation question
  | .gaussian failure => .gaussian failure

/-- Forward an original tagged Gaussian request in the same combined query surface. -/
private def gaussianHandler (question : Real.Observation.Query) :
    Program (Question input) (Reply input) (Except PointError Real.Observation.Reply) :=
  .request (.inr (.inl question)) fun answer => match answer with
    | .inr (.inl reply) => .pure (.ok reply)
    | _ => .pure (.error (.operation question))

/-- Attach the actual returned numerical point using its original tagged Gaussian operation. -/
private def attach (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    Program (Question input) (Reply input) (Except PointFailure (Real.Paired.PointState point unit)) :=
  ((Real.Paired.attach point unit).substituteChecked (gaussianHandler input)).map fun result =>
    match result with
    | .error invalid => .error invalid.toFailure
    | .ok execution => execution.value.mapError PointFailure.gaussian

/-- The original imaginary-coordinate reply for a retained paired point. -/
private abbrev ImaginaryResult (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : Real.Paired.PointState point unit) (request : AccuracyRequest) :=
  Coordinate.Observation.CertifiedState Norm.Coordinates.im_sub_sq_le_basic_normSq
    saved.paired.imaginaryAtCurrent request.tolerance request.positive

/-- The original imaginary-coordinate failure and any actual returned refinement. -/
private abbrev ImaginaryFailure (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : Real.Paired.PointState point unit) (request : AccuracyRequest) :=
  Coordinate.Observation.CoordinateFailure saved.paired.imaginaryAtCurrent request.tolerance request.positive PointError

/-- Continue the actual paired state, reusing a matching returned imaginary refinement when present. -/
private def advance (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : Real.Paired.PointState point unit) : Program (Question input) (Reply input)
      (Except (PointFailure × Option (Real.Paired.PointState point unit)) (Real.Paired.PointState point unit)) :=
  if saved.paired.imaginary.interval.width < input.imaginary.tolerance then .pure (.ok saved)
  else
    let ask := Real.Observation.checkedWith (Real.Paired.tag point unit) (gaussianHandler input) PointError.gaussian
    let finish (result : Except (ImaginaryFailure point unit saved input.imaginary)
        (ImaginaryResult point unit saved input.imaginary)) :
        Except (PointFailure × Option (Real.Paired.PointState point unit)) (Real.Paired.PointState point unit) :=
      match result with
      | .error (.refinement reason) => .error (reason.toFailure, some saved)
      | .error (.ball next reason) =>
          .error (.pending ⟨point, unit, saved, input.imaginary, next⟩ reason, some saved)
      | .ok next => .ok (Real.Paired.withImaginary point unit saved input.imaginary
          (Coordinate.Observation.assembleImaginary saved.paired input.imaginary.tolerance
            input.imaginary.positive next))
    match Pending.matching input.pending point unit saved input.imaginary with
    | some next => (Coordinate.Observation.resumeWith ask Norm.Coordinates.im_sub_sq_le_basic_normSq
        saved.paired.imaginaryAtCurrent input.imaginary.tolerance input.imaginary.positive next).map finish
    | none => (Coordinate.Observation.coordinateWith ask Norm.Coordinates.im_sub_sq_le_basic_normSq
        saved.paired.imaginaryAtCurrent input.imaginary.tolerance input.imaginary.positive).map finish

/-- Observe one original numerical point using the shared saved-pair branch logic. -/
private def observe (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (bank : List Real.Paired.Frontier.Saved) :=
  Real.Paired.Frontier.observeWith point unit bank (attach input point unit) (advance input point unit)

set_option genInjectivity false in
/-- Paired work on the actual returned frontier, including an interrupted occurrence. -/
structure FrontierProgress (frontier : NumericalFrontier Horner.Real.source) where
  /-- Successfully paired original frontier cells, in occurrence order. -/
  completed : List (Real.Paired.Frontier.Completed frontier)
  /-- The remaining actual frontier occurrences. -/
  pending : List (Real.Paired.Frontier.Occurrence frontier)
  /-- The bank retaining successful and partially attached paired states. -/
  bank : List Real.Paired.Frontier.Saved
  /-- The first failed operation, if one occurred. -/
  failure : Option PointFailure

/-- Observe the ordered cells of the exact returned numerical frontier. -/
def frontier (frontier : NumericalFrontier Horner.Real.source) (bank : List Real.Paired.Frontier.Saved) :=
  Real.Paired.Frontier.visitWith frontier (observe input)
    (fun completed bank => FrontierProgress.mk completed [] bank none)
    (fun completed pending bank failure => FrontierProgress.mk completed pending bank (some failure))
    (Real.Paired.Frontier.occurrences frontier) [] bank

/-- One exact returned common-reading occurrence. -/
abbrev CommonOccurrence (result : Numerical.Result input.mixed) :=
  {reading : CommonReading (Numerical.exactFrontier input.mixed result.production) result.numerical.state.1
      input.mixed.pointRequest // reading ∈ result.common.readings}

/-- The actual right common point belongs to its original unit child. -/
theorem commonPoint_unit (result : Numerical.Result input.mixed) (occurrence : CommonOccurrence input result) :
    0 ≤ occurrence.val.rightPoint.point ∧ occurrence.val.rightPoint.point ≤ 1 := by
  let reading := occurrence.val
  have tag_eq : reading.rightPoint.point = reading.tag := by
    rw [reading.right_point_eq]
    rfl
  rw [tag_eq]
  exact ⟨Fraction.Order.Basic.le_trans _ _ _ reading.valid.1 reading.tag_inside.1,
    Fraction.Order.Basic.le_trans _ _ _ reading.tag_inside.2 reading.valid.2.2⟩

set_option genInjectivity false in
/-- A paired state belonging to one actual returned mixed common point. -/
structure CommonCompleted (result : Numerical.Result input.mixed) where
  /-- The original returned common-reading occurrence. -/
  occurrence : CommonOccurrence input result
  /-- The paired point retains that occurrence's original numerical state. -/
  state : Real.Paired.PointState occurrence.val.rightPoint (commonPoint_unit input result occurrence)

/-- The returned common pair bounds the finite Taylor sample at its actual numerical point. -/
theorem CommonCompleted.sample_midpoint_normSq_le (result : Numerical.Result input.mixed)
    (entry : CommonCompleted input result) :
    Norm.Basic.normSq (Horner.Sample.sample (RationalEmbedding.realPoint entry.occurrence.val.rightPoint.point)
      result.production.comparison.receipt.selection.depth - entry.state.paired.midpoint) ≤
        (entry.state.paired.real.interval.width +
          Horner.Real.tailRadius result.production.comparison.receipt.selection.depth) ^ 2 +
          (entry.state.paired.imaginary.interval.width * (1 / 2)) ^ 2 :=
  Real.Paired.finiteSample_midpoint_normSq_le entry.occurrence.val.rightPoint
    (commonPoint_unit input result entry.occurrence) entry.state result.production.comparison.receipt.selection.depth

/-- Both returned common observations retain the same actual rational child tag. -/
theorem commonPoints_same (result : Numerical.Result input.mixed) (occurrence : CommonOccurrence input result) :
    occurrence.val.leftPoint.point = occurrence.val.rightPoint.point := by
  let reading := occurrence.val
  have left : reading.leftPoint.point = reading.tag := by
    rw [reading.left_point_eq]
    rfl
  have right : reading.rightPoint.point = reading.tag := by
    rw [reading.right_point_eq]
    rfl
  exact left.trans right.symm

/-- The actual finite-source common reading is the selected Taylor value at the paired numerical tag. -/
theorem CommonCompleted.finite_reading (result : Numerical.Result input.mixed)
    (entry : CommonCompleted input result) :
    entry.occurrence.val.leftPoint.reading = Purelib.Data.Rat.Interval.exact
      (Horner.Real.finiteSource result.production.comparison.receipt.selection.depth
        entry.occurrence.val.rightPoint.point) := by
  rw [entry.occurrence.val.leftPoint.reading_eq]
  change Purelib.Data.Rat.Interval.exact
    (Horner.Real.finiteSource result.production.comparison.receipt.selection.depth
      entry.occurrence.val.leftPoint.point) = _
  rw [commonPoints_same input result entry.occurrence]

set_option genInjectivity false in
/-- Paired work on the actual mixed common points and any unfinished occurrence. -/
structure CommonProgress (result : Numerical.Result input.mixed) where
  /-- Completed original common occurrences, in original order. -/
  completed : List (CommonCompleted input result)
  /-- Original common occurrences still to process. -/
  pending : List (CommonOccurrence input result)
  /-- The actual bank of original paired states. -/
  bank : List Real.Paired.Frontier.Saved
  /-- The first failed operation, if one occurred. -/
  failure : Option PointFailure

/-- Visit the returned common points without rebuilding the mixed comparison. -/
private def commonVisit (result : Numerical.Result input.mixed) :
    List (CommonOccurrence input result) → List (CommonCompleted input result) → List Real.Paired.Frontier.Saved →
      Program (Question input) (Reply input) (CommonProgress input result)
  | [], completed, bank => .pure ⟨completed.reverse, [], bank, none⟩
  | occurrence :: rest, completed, bank =>
      let point := occurrence.val.rightPoint
      let unit := commonPoint_unit input result occurrence
      (observe input point unit bank).bind fun outcome => match outcome with
        | .error (failure, acquired) =>
            let retained := match acquired with
              | none => bank
              | some saved => ⟨point, unit, saved⟩ :: bank
            .pure ⟨completed.reverse, occurrence :: rest, retained, some failure⟩
        | .ok saved => commonVisit result rest (⟨occurrence, saved⟩ :: completed) (⟨point, unit, saved⟩ :: bank)

/-- Observe the exact returned ordered common-reading points. -/
def common (result : Numerical.Result input.mixed) (bank : List Real.Paired.Frontier.Saved) :=
  commonVisit input result result.common.readings.attach [] bank

/-- An identity forwarding action used to retain each actual original execution and trace. -/
private def forward (question : Question input) :
    Program (Question input) (Reply input) (Except Empty (Reply input)) :=
  .request question fun reply => .pure (.ok reply)

/-- Retain the original value and ordered trace without adding a source request. -/
private def record {Value : Type} (program : Program (Question input) (Reply input) Value) :=
  program.substituteChecked (forward input)

/-- The forwarding action preserves the exact original reply at every displayed operation. -/
private theorem forward_original (oracle : Question input → Reply input) (question : Question input) :
    ((forward input question).protocol.run oracle).value = .ok (oracle question) := rfl

/-- Recording retains the complete original execution for every reply oracle. -/
private theorem record_value {Value : Type} (program : Program (Question input) (Reply input) Value)
    (oracle : Question input → Reply input) :
    ((record input program).protocol.run oracle).value = .ok (program.protocol.run oracle) := by
  unfold record
  apply Program.substituteChecked_value
  exact forward_original input oracle

/-- Original combined replies answer each paired Gaussian operation from that same original point. -/
private theorem gaussianHandler_original (question : Real.Observation.Query) :
    ((gaussianHandler input question).protocol.run (Numerical.originalReply input.mixed)).value =
      .ok (Real.Observation.original question) := rfl

/-- Original combined replies attach the actual original numerical point. -/
private theorem attach_original (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    ((attach input point unit).protocol.run (Numerical.originalReply input.mixed)).value =
      .ok (Real.Paired.originalAttached point unit) := by
  unfold attach
  rw [Program.map_execution, Protocol.map_run_value]
  have original := Program.substituteChecked_value (gaussianHandler input) (Real.Paired.attach point unit)
    (Numerical.originalReply input.mixed) Real.Observation.original (gaussianHandler_original input)
  rw [original]
  dsimp only
  rw [Real.Paired.attach_original]
  rfl

/-- Original replies continue or resume the same exact imaginary-coordinate request. -/
private theorem advance_original (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : Real.Paired.PointState point unit) :
    ((advance input point unit saved).protocol.run (Numerical.originalReply input.mixed)).value =
      .ok (if saved.paired.imaginary.interval.width < input.imaginary.tolerance then saved
        else Real.Paired.requestedState point unit saved input.imaginary) := by
  let tag := Real.Paired.tag point unit
  let ask := Real.Observation.checkedWith tag (gaussianHandler input) PointError.gaussian
  have answers (operation : Coordinate.Observation.Request (Real.Observation.process tag).State) :
      ((ask operation).protocol.run (Numerical.originalReply input.mixed)).value =
        .ok (Coordinate.Observation.original_request (Real.Observation.process tag) operation ▸
          (Coordinate.Observation.original (Real.Observation.process tag) operation).2) :=
    Real.Observation.checkedWith_original tag (gaussianHandler input) PointError.gaussian operation
      (Numerical.originalReply input.mixed) (gaussianHandler_original input)
  unfold advance
  by_cases adequate : saved.paired.imaginary.interval.width < input.imaginary.tolerance
  · rw [if_pos adequate, if_pos adequate]
    rfl
  · rw [if_neg adequate, if_neg adequate]
    cases found : Pending.matching input.pending point unit saved input.imaginary with
    | none =>
        dsimp only
        rw [Program.map_execution, Protocol.map_run_value]
        rw [Coordinate.Observation.coordinateWith_original ask Norm.Coordinates.im_sub_sq_le_basic_normSq
          saved.paired.imaginaryAtCurrent input.imaginary.tolerance input.imaginary.positive
          (Numerical.originalReply input.mixed) answers]
        apply congrArg Except.ok
        apply congrArg (Real.Paired.withImaginary point unit saved input.imaginary)
        apply Subtype.ext
        exact (Coordinate.Observation.assembleImaginary saved.paired input.imaginary.tolerance
          input.imaginary.positive _).property
    | some next =>
        dsimp only
        rw [Program.map_execution, Protocol.map_run_value]
        rw [Coordinate.Observation.resumeWith_original ask Norm.Coordinates.im_sub_sq_le_basic_normSq
          saved.paired.imaginaryAtCurrent input.imaginary.tolerance input.imaginary.positive next
          (Numerical.originalReply input.mixed) answers]
        apply congrArg Except.ok
        apply congrArg (Real.Paired.withImaginary point unit saved input.imaginary)
        apply Subtype.ext
        exact (Coordinate.Observation.assembleImaginary saved.paired input.imaginary.tolerance
          input.imaginary.positive _).property

/-- Original replies make the same cached paired-point choice and meet the requested width. -/
private theorem observe_original_accurate (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (bank : List Real.Paired.Frontier.Saved) :
    ∃ next, ((observe input point unit bank).protocol.run (Numerical.originalReply input.mixed)).value = .ok next ∧
      next.paired.imaginary.interval.width < input.imaginary.tolerance := by
  have complete (saved : Real.Paired.PointState point unit) :
      ∃ next, ((advance input point unit saved).protocol.run (Numerical.originalReply input.mixed)).value =
        .ok next ∧ next.paired.imaginary.interval.width < input.imaginary.tolerance := by
    by_cases adequate : saved.paired.imaginary.interval.width < input.imaginary.tolerance
    · refine ⟨saved, ?_, adequate⟩
      rw [advance_original, if_pos adequate]
    · refine ⟨Real.Paired.requestedState point unit saved input.imaginary, ?_, ?_⟩
      · rw [advance_original, if_neg adequate]
      · exact saved.paired.requestImaginary_accurate input.imaginary.tolerance input.imaginary.positive
  cases found : Real.Paired.Frontier.findState point unit bank with
  | some saved =>
      unfold observe Real.Paired.Frontier.observeWith
      rw [found]
      exact complete saved
  | none =>
      cases origin : Real.Paired.Frontier.findOrigin point unit bank with
      | some ball =>
          unfold observe Real.Paired.Frontier.observeWith
          rw [found, origin]
          exact complete (Real.Paired.Frontier.fromOrigin point unit ball)
      | none =>
          obtain ⟨next, value, accurate⟩ := complete (Real.Paired.originalAttached point unit)
          refine ⟨next, ?_, accurate⟩
          unfold observe Real.Paired.Frontier.observeWith
          rw [found, origin, Program.bind_execution, Protocol.bind_run_value, attach_original]
          exact value

/-- Recording makes exactly the same ordered source requests as the original program. -/
private theorem record_trace {Value : Type} (program : Program (Question input) (Reply input) Value)
    (oracle : Question input → Reply input) :
    ((record input program).protocol.run oracle).trace = (program.protocol.run oracle).trace := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      have tail := induction (oracle question)
      change (((next (oracle question)).substituteChecked (forward input)).protocol.run oracle).trace =
        ((next (oracle question)).protocol.run oracle).trace at tail
      unfold record
      rw [Program.substituteChecked, Program.checkedStep, Program.bind_execution, Protocol.bind_run_trace]
      let tag (result : Except Empty (Basic.Execution (Question input) (Reply input) Value)) :=
        result.map fun after =>
          (⟨after.value, ⟨question, oracle question⟩ :: after.trace⟩ :
            Basic.Execution (Question input) (Reply input) Value)
      change (⟨question, oracle question⟩ : Basic.Exchange (Question input) (Reply input)) ::
        (((((next (oracle question)).substituteChecked (forward input)).map tag).protocol.run oracle).trace) =
          ⟨question, oracle question⟩ :: ((next (oracle question)).protocol.run oracle).trace
      rw [Program.map_execution, Protocol.map_run_trace, tail]

/-- Original replies finish an ordered visit of the actual frontier occurrences. -/
private theorem frontier_visit_original_finished (frontier : NumericalFrontier Horner.Real.source)
    (remaining : List (Real.Paired.Frontier.Occurrence frontier))
    (completed : List (Real.Paired.Frontier.Completed frontier)) (bank : List Real.Paired.Frontier.Saved) :
    let progress := ((Real.Paired.Frontier.visitWith frontier (observe input)
      (fun completed bank => FrontierProgress.mk completed [] bank none)
      (fun completed pending bank failure => FrontierProgress.mk completed pending bank (some failure))
      remaining completed bank).protocol.run (Numerical.originalReply input.mixed)).value
    progress.pending = [] ∧ progress.failure = none := by
  induction remaining generalizing completed bank with
  | nil => exact ⟨rfl, rfl⟩
  | cons occurrence rest induction =>
      let point := occurrence.val.item
      let unit := Real.Paired.Frontier.pointUnit frontier occurrence.val occurrence.property
      obtain ⟨next, returned, _⟩ := observe_original_accurate input point unit bank
      rw [Real.Paired.Frontier.visitWith, Program.bind_execution, Protocol.bind_run_value, returned]
      exact induction (⟨occurrence, next⟩ :: completed) (⟨point, unit, next⟩ :: bank)

/-- Original replies finish the actual ordered frontier and preserve its returned bank. -/
private theorem frontier_original_finished (numericalFrontier : NumericalFrontier Horner.Real.source)
    (bank : List Real.Paired.Frontier.Saved) :
    let progress := ((frontier input numericalFrontier bank).protocol.run (Numerical.originalReply input.mixed)).value
    progress.pending = [] ∧ progress.failure = none :=
  frontier_visit_original_finished input numericalFrontier (Real.Paired.Frontier.occurrences numericalFrontier) [] bank

/-- Original replies finish an ordered visit of the actual returned common points. -/
private theorem commonVisit_original_finished (result : Numerical.Result input.mixed)
    (remaining : List (CommonOccurrence input result)) (completed : List (CommonCompleted input result))
    (bank : List Real.Paired.Frontier.Saved) :
    let progress := ((commonVisit input result remaining completed bank).protocol.run
      (Numerical.originalReply input.mixed)).value
    progress.pending = [] ∧ progress.failure = none := by
  induction remaining generalizing completed bank with
  | nil => exact ⟨rfl, rfl⟩
  | cons occurrence rest induction =>
      let point := occurrence.val.rightPoint
      let unit := commonPoint_unit input result occurrence
      obtain ⟨next, returned, _⟩ := observe_original_accurate input point unit bank
      rw [commonVisit, Program.bind_execution, Protocol.bind_run_value, returned]
      exact induction (⟨occurrence, next⟩ :: completed) (⟨point, unit, next⟩ :: bank)

/-- Original replies finish the actual ordered common-point observations. -/
private theorem common_original_finished (result : Numerical.Result input.mixed)
    (bank : List Real.Paired.Frontier.Saved) :
    let progress := ((common input result bank).protocol.run (Numerical.originalReply input.mixed)).value
    progress.pending = [] ∧ progress.failure = none :=
  commonVisit_original_finished input result result.common.readings.attach [] bank

/-- The actual full execution of the original mixed runner. -/
abbrev MixedExecution := Basic.Execution (Question input) (Reply input)
  (Except (Numerical.Failure input.mixed) (Numerical.Result input.mixed))

/-- The actual paired-frontier execution, including its ordered Gaussian requests. -/
abbrev FrontierExecution (result : Numerical.Result input.mixed) :=
  Basic.Execution (Question input) (Reply input) (FrontierProgress result.numerical.state.1)

/-- The actual common-point pairing execution, including its ordered Gaussian requests. -/
abbrev CommonExecution (result : Numerical.Result input.mixed) :=
  Basic.Execution (Question input) (Reply input) (CommonProgress input result)

set_option genInjectivity false in
/-- The original mixed result and the exact paired frontier/common progress. -/
inductive Outcome where
  /-- The original mixed runner failed with its typed saved work. -/ | mixed
      (execution : MixedExecution input) (failure : Numerical.Failure input.mixed)
      (same : execution.value = .error failure)
  /-- Pairing stopped on an actual frontier occurrence with its completed work. -/ | frontier
      (execution : MixedExecution input) (result : Numerical.Result input.mixed)
      (same : execution.value = .ok result) (progress : FrontierExecution input result)
  /-- Pairing retained both original executions and the actual common-point progress. -/ | common
      (execution : MixedExecution input) (result : Numerical.Result input.mixed)
      (same : execution.value = .ok result) (frontier : FrontierExecution input result)
      (progress : CommonExecution input result)

/-- The actual ordered requests retained by each completed stage of a paired outcome. -/
@[expose] def Outcome.trace (outcome : Outcome input) : List (Basic.Exchange (Question input) (Reply input)) :=
  match outcome with
  | .mixed execution _ _ => execution.trace
  | .frontier execution _ _ frontierExecution => execution.trace ++ frontierExecution.trace
  | .common execution _ _ frontierExecution commonExecution =>
      execution.trace ++ (frontierExecution.trace ++ commonExecution.trace)

/-- The number of all displayed operations retained by the actual completed stages. -/
@[expose] def Outcome.requestCount (outcome : Outcome input) : Nat := (Outcome.trace input outcome).length

/-- The actual tagged Gaussian operations issued after the mixed computation. -/
@[expose] def Outcome.pairedRequestCount (outcome : Outcome input) : Nat :=
  match outcome with
  | .mixed _ _ _ => 0
  | .frontier _ _ _ frontierExecution => frontierExecution.trace.length
  | .common _ _ _ frontierExecution commonExecution => frontierExecution.trace.length + commonExecution.trace.length

/-- Compose the original mixed runner with its actual returned frontier and common point pairs. -/
def computation : Program (Question input) (Reply input) (Outcome input) :=
  (record input (Numerical.computation input.mixed)).bind fun mixed => match mixed with
    | .error impossible => nomatch impossible
    | .ok execution => match same : execution.value with
      | .error failure => .pure (.mixed execution failure same)
      | .ok result => (record input (frontier input result.numerical.state.1 input.bank)).bind fun recorded =>
          match recorded with
          | .error impossible => nomatch impossible
          | .ok first => match first.value.failure with
            | some _ => .pure (.frontier execution result same first)
            | none => (record input (common input result first.value.bank)).map fun recordedCommon =>
                match recordedCommon with
                | .error impossible => nomatch impossible
                | .ok second => .common execution result same first second

/-- The combined trace is exactly the concatenation retained in its actual outcome. -/
theorem computation_trace (oracle : Question input → Reply input) :
    let execution := (computation input).protocol.run oracle
    execution.trace = Outcome.trace input execution.value := by
  unfold computation
  dsimp only
  conv_lhs => rw [Program.bind_execution, Protocol.bind_run_trace, record_trace, record_value]
  conv_rhs => rw [Program.bind_execution, Protocol.bind_run_value, record_value]
  dsimp only
  split
  next failure same =>
    change _ ++ [] = _
    exact Purelib.Data.List.Append.append_nil _
  next result same =>
    conv_lhs => rw [Program.bind_execution, Protocol.bind_run_trace, record_trace, record_value]
    conv_rhs => rw [Program.bind_execution, Protocol.bind_run_value, record_value]
    dsimp only
    split
    next failure stopped =>
      change _ ++ (_ ++ []) = _ ++ _
      rw [Purelib.Data.List.Append.append_nil]
    next completed =>
      conv_lhs => rw [Program.map_execution, Protocol.map_run_trace, record_trace]
      conv_rhs => rw [Program.map_execution, Protocol.map_run_value, record_value]
      rfl

/-- The outcome counts exactly the operations in the displayed combined execution. -/
theorem computation_requestCount (oracle : Question input → Reply input) :
    let execution := (computation input).protocol.run oracle
    Outcome.requestCount input execution.value = execution.trace.length := by
  exact congrArg List.length (computation_trace input oracle).symm

/-- A successful mixed run and completed frontier select their exact paired common execution. -/
private theorem computation_success (oracle : Question input → Reply input)
    (result : Numerical.Result input.mixed)
    (same : ((Numerical.computation input.mixed).protocol.run oracle).value = .ok result)
    (finished : ((frontier input result.numerical.state.1 input.bank).protocol.run oracle).value.failure = none) :
    ((computation input).protocol.run oracle).value =
      .common ((Numerical.computation input.mixed).protocol.run oracle) result same
        ((frontier input result.numerical.state.1 input.bank).protocol.run oracle)
        ((common input result
          ((frontier input result.numerical.state.1 input.bank).protocol.run oracle).value.bank).protocol.run
            oracle) := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, record_value]
  let execution := (Numerical.computation input.mixed).protocol.run oracle
  change (((match found : execution.value with
    | .error failure => (Program.pure (.mixed execution failure found) :
        Program (Question input) (Reply input) (Outcome input))
    | .ok returned => (record input (frontier input returned.numerical.state.1 input.bank)).bind fun
        (recorded : Except Empty (FrontierExecution input returned)) =>
        match recorded with
        | .error impossible => nomatch impossible
        | .ok first => match first.value.failure with
          | some _ => .pure (.frontier execution returned found first)
          | none => (record input (common input returned first.value.bank)).map fun
              (recordedCommon : Except Empty (CommonExecution input returned)) =>
              match recordedCommon with
              | .error impossible => nomatch impossible
              | .ok second => .common execution returned found first second).protocol.run oracle).value) =
    .common execution result same ((frontier input result.numerical.state.1 input.bank).protocol.run oracle)
      ((common input result
        ((frontier input result.numerical.state.1 input.bank).protocol.run oracle).value.bank).protocol.run oracle)
  change execution.value = .ok result at same
  revert same
  cases execution with
  | mk value trace =>
      cases value with
      | error failure => intro same; cases same
      | ok returned =>
          intro same
          cases same
          rw [Program.bind_execution, Protocol.bind_run_value, record_value]
          dsimp only
          rw [finished, Program.map_execution, Protocol.map_run_value, record_value]

/-- Original replies complete the mixed runner and both paired visits on their actual returned owners. -/
theorem computation_original :
    ∃ (execution : MixedExecution input) (result : Numerical.Result input.mixed)
      (same : execution.value = .ok result) (first : FrontierExecution input result)
      (second : CommonExecution input result),
      ((computation input).protocol.run (Numerical.originalReply input.mixed)).value =
        .common execution result same first second ∧
      execution = (Numerical.computation input.mixed).protocol.run (Numerical.originalReply input.mixed) ∧
      first = (frontier input result.numerical.state.1 input.bank).protocol.run
        (Numerical.originalReply input.mixed) ∧
      second = (common input result first.value.bank).protocol.run (Numerical.originalReply input.mixed) ∧
      first.value.pending = [] ∧ first.value.failure = none ∧
      second.value.pending = [] ∧ second.value.failure = none := by
  obtain ⟨result, returned, _⟩ := Numerical.computation_original input.mixed
  let execution := (Numerical.computation input.mixed).protocol.run (Numerical.originalReply input.mixed)
  have same : execution.value = .ok result := returned
  let first := (frontier input result.numerical.state.1 input.bank).protocol.run
    (Numerical.originalReply input.mixed)
  let second := (common input result first.value.bank).protocol.run (Numerical.originalReply input.mixed)
  have firstDone := frontier_original_finished input result.numerical.state.1 input.bank
  have secondDone := common_original_finished input result first.value.bank
  exact ⟨execution, result, same, first, second,
    computation_success input (Numerical.originalReply input.mixed) result same firstDone.2,
    rfl, rfl, rfl, firstDone.1, firstDone.2, secondDone.1, secondDone.2⟩

/-- Continue either completed or interrupted paired work using the exact returned mixed result and pair bank. -/
@[expose] def Outcome.continuation (outcome : Outcome input) (runnerRequest : CertifiedProgram.Request)
    (count : Nat) (productionAccuracy numericalRequest pointRequest imaginary : AccuracyRequest) :
    Option (Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :=
  match outcome with
  | .mixed _ _ _ => none
  | .frontier _ result _ progress =>
      let pending := match progress.value.failure with
        | some (.pending receipt _) => some receipt
        | _ => input.pending
      some ⟨Numerical.Result.continuation input.mixed result runnerRequest count productionAccuracy
        numericalRequest pointRequest, imaginary, progress.value.bank, pending⟩
  | .common _ result _ _ progress =>
      let pending := match progress.value.failure with
        | some (.pending receipt _) => some receipt
        | _ => input.pending
      some ⟨Numerical.Result.continuation input.mixed result runnerRequest count productionAccuracy
        numericalRequest pointRequest, imaginary, progress.value.bank, pending⟩

/-- Replay preserves the actual mixed execution, paired progress and first failure. -/
theorem replay (oracle : Question input → Reply input) :
    (computation input).protocol.replayExact ((computation input).protocol.run oracle).trace =
      .ok ((computation input).protocol.run oracle).value :=
  (computation input).protocol.replayExact_run oracle

/-- Replies outside the combined trace cannot affect the returned progress or displayed operations. -/
theorem payload_erasure {Payload : Type} (oracle : Question input → Reply input) (payload : Payload)
    (outside : Payload → Question input → Reply input) :
    (computation input).protocol.run (Boundary.Trace.overlay
      ((computation input).protocol.run oracle).trace (outside payload)) = (computation input).protocol.run oracle :=
  (computation input).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Paired

end
