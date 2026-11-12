module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous
public import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation
public import Purelib.Integration.Polynomial.Gaussian.Partition.Compiled
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing the original ordered polynomial path

Every question retains its original segment occurrence and coordinate. The
requests follow the original additive bound process, including the recursive
halving of each supplied rational accuracy demand.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic
open Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation
  (originalReply realConstruction imaginaryConstruction realConstruction_original imaginaryConstruction_original
    realModulus imaginaryModulus realPreparation imaginaryPreparation)
open Purelib.Integration.SourceFrontier.Continuous
open Purelib.Integration.SourceFrontier.Continuous.Observation

/-- The exact half-tolerance used by each original additive bound process. -/
@[expose] def half (request : AccuracyRequest) : AccuracyRequest :=
  ⟨request.tolerance / 2, Fraction.Order.Field.div_pos_direct request.positive (by decide)⟩

/-- A saved real-coordinate state of the original ordered source path. -/
abbrev RealState (source : Source.PolynomialPath) := (boundProcess source).State

/-- A saved imaginary-coordinate state of the original ordered source path. -/
abbrev ImaginaryState (source : Source.PolynomialPath) := (imaginaryBoundProcess source).State

/-- A question for both coordinates of one original polynomial segment. -/
abbrev SegmentQuery (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest) :=
  Partition.Continuous.Observation.Query source realRequest imaginaryRequest

/-- A question retains the source segment's exact occurrence and coordinate. -/
@[expose] def Query : Source.PolynomialPath → AccuracyRequest → AccuracyRequest → Type
  | [], _, _ => Empty
  | source :: remaining, realRequest, imaginaryRequest =>
      Sum (SegmentQuery source (half realRequest) (half imaginaryRequest))
        (Query remaining (half realRequest) (half imaginaryRequest))

/-- A reply retains the source segment occurrence and its original coordinate owner. -/
@[expose] def Reply : Source.PolynomialPath → Type
  | [] => Empty
  | source :: remaining => Sum (Partition.Continuous.Observation.Reply source) (Reply remaining)

/-- Equality of displayed path questions is executable from their finite indices. -/
@[expose] def queryDecidableEq : ∀ (source : Source.PolynomialPath) (realRequest imaginaryRequest : AccuracyRequest),
    DecidableEq (Query source realRequest imaginaryRequest)
  | [], _, _ => fun question => nomatch question
  | source :: remaining, realRequest, imaginaryRequest => by
      change DecidableEq (Sum (SegmentQuery source (half realRequest)
        (half imaginaryRequest)) (Query remaining (half realRequest) (half imaginaryRequest)))
      letI := queryDecidableEq remaining (half realRequest) (half imaginaryRequest)
      infer_instance

/-- Path-question equality uses the retained finite source occurrence. -/
instance (source : Source.PolynomialPath) (realRequest imaginaryRequest : AccuracyRequest) :
    DecidableEq (Query source realRequest imaginaryRequest) := queryDecidableEq source realRequest imaginaryRequest

set_option genInjectivity false in
/-- A failed ordered-path request records the actual owner mismatch or segment obstruction. -/
inductive Failure : (source : Source.PolynomialPath) → AccuracyRequest → AccuracyRequest → Type where
  /-- A reply belongs to a different source-segment occurrence. -/
  | owner {source realRequest imaginaryRequest} (question : Query source realRequest imaginaryRequest) :
      Failure source realRequest imaginaryRequest
  /-- The head segment's original coordinate request failed. -/
  | head {source remaining realRequest imaginaryRequest}
      (invalid : Partition.Continuous.Observation.Failure source (half realRequest) (half imaginaryRequest)) :
      Failure (source :: remaining) realRequest imaginaryRequest
  /-- A request in the original remaining path failed. -/
  | tail {source remaining realRequest imaginaryRequest}
      (invalid : Failure remaining (half realRequest) (half imaginaryRequest)) :
      Failure (source :: remaining) realRequest imaginaryRequest

constructive_injectivity Failure

/-- Each original segment answers its own retained path occurrence. -/
@[expose] def pathReply : ∀ (source : Source.PolynomialPath) (realRequest imaginaryRequest : AccuracyRequest),
    Query source realRequest imaginaryRequest → Reply source
  | [], _, _, question => nomatch question
  | source :: _, realRequest, imaginaryRequest, .inl question =>
      .inl (originalReply source (half realRequest) (half imaginaryRequest) question)
  | _ :: remaining, realRequest, imaginaryRequest, .inr question =>
      .inr (pathReply remaining (half realRequest) (half imaginaryRequest) question)

/-- Display a head-segment question and reject a reply from a different path occurrence. -/
@[expose] def headHandler (source : PolynomialSegment) (remaining : Source.PolynomialPath)
    (realRequest imaginaryRequest : AccuracyRequest)
    (question : SegmentQuery source (half realRequest) (half imaginaryRequest)) :
    Program (Query (source :: remaining) realRequest imaginaryRequest) (Reply (source :: remaining))
      (Except (Failure (source :: remaining) realRequest imaginaryRequest)
        (Partition.Continuous.Observation.Reply source)) :=
  .request (.inl question) fun reply =>
    match reply with
    | .inl point => .pure (.ok point)
    | .inr _ => .pure (.error (.owner (.inl question)))

/-- Display a tail question and reject a reply from the head occurrence. -/
@[expose] def tailHandler (source : PolynomialSegment) (remaining : Source.PolynomialPath)
    (realRequest imaginaryRequest : AccuracyRequest)
    (question : Query remaining (half realRequest) (half imaginaryRequest)) :
    Program (Query (source :: remaining) realRequest imaginaryRequest) (Reply (source :: remaining))
      (Except (Failure (source :: remaining) realRequest imaginaryRequest) (Reply remaining)) :=
  .request (.inr question) fun reply =>
    match reply with
    | .inl _ => .pure (.error (.owner (.inr question)))
    | .inr point => .pure (.ok point)

/-- Resume every original real-coordinate segment history in source order.

The same half-tolerance allocation and saved states are used by the original
additive bound process. Each successful head state is retained before the
remaining path is requested; a typed failure stops the actual continuation. -/
@[expose] def realComputation : ∀ (source : Source.PolynomialPath) (_state : RealState source)
    (realRequest imaginaryRequest : AccuracyRequest),
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (RealState source))
  | [], state, _, _ => .pure (.ok state)
  | source :: remaining, state, realRequest, imaginaryRequest =>
      ((realConstruction source state.1
          (half realRequest) (half imaginaryRequest)).substituteChecked
          (headHandler source remaining realRequest imaginaryRequest)).bind fun first =>
        match first with
        | .error invalid => .pure (.error invalid)
        | .ok execution =>
          match execution.value with
          | .error invalid => .pure (.error (.head invalid))
          | .ok inner =>
            match inner.value with
            | .error invalid => .pure (.error (.head (.real invalid)))
            | .ok nextHead =>
              ((realComputation remaining state.2 (half realRequest) (half imaginaryRequest)).substituteChecked
                  (tailHandler source remaining realRequest imaginaryRequest)).map fun result =>
                match result with
                | .error invalid => .error invalid
                | .ok tailExecution =>
                  match tailExecution.value with
                  | .error invalid => .error (.tail invalid)
                  | .ok nextTail => .ok (nextHead, nextTail)

/-- Resume every original imaginary-coordinate segment history in source order.

The same half-tolerance allocation and saved states are used by the original
additive bound process. A failure retains its original path occurrence and
prevents later source requests. -/
@[expose] def imaginaryComputation : ∀ (source : Source.PolynomialPath) (_state : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest),
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (ImaginaryState source))
  | [], state, _, _ => .pure (.ok state)
  | source :: remaining, state, realRequest, imaginaryRequest =>
      ((imaginaryConstruction source state.1
          (half realRequest) (half imaginaryRequest)).substituteChecked
          (headHandler source remaining realRequest imaginaryRequest)).bind fun first =>
        match first with
        | .error invalid => .pure (.error invalid)
        | .ok execution =>
          match execution.value with
          | .error invalid => .pure (.error (.head invalid))
          | .ok inner =>
            match inner.value with
            | .error invalid => .pure (.error (.head (.imaginary invalid)))
            | .ok nextHead =>
              ((imaginaryComputation remaining state.2 (half realRequest) (half imaginaryRequest)).substituteChecked
                  (tailHandler source remaining realRequest imaginaryRequest)).map fun result =>
                match result with
                | .error invalid => .error invalid
                | .ok tailExecution =>
                  match tailExecution.value with
                  | .error invalid => .error (.tail invalid)
                  | .ok nextTail => .ok (nextHead, nextTail)

/-- Request the original real path followed by the original imaginary path.

The two requests retain their independent saved states and source order. The
second begins only after the first has returned its actual continued state. -/
@[expose] def computation (source : Source.PolynomialPath) (real : RealState source)
    (imaginary : ImaginaryState source) (realRequest imaginaryRequest : AccuracyRequest) :
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (RealState source × ImaginaryState source)) :=
  (realComputation source real realRequest imaginaryRequest).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok nextReal => (imaginaryComputation source imaginary realRequest imaginaryRequest).map fun second =>
        second.map fun nextImaginary => (nextReal, nextImaginary)

/-- The head handler returns the exact original segment's reply. -/
theorem headHandler_original (source : PolynomialSegment) (remaining : Source.PolynomialPath)
    (realRequest imaginaryRequest : AccuracyRequest)
    (question : SegmentQuery source (half realRequest) (half imaginaryRequest)) :
    ((headHandler source remaining realRequest imaginaryRequest question).protocol.run
      (pathReply (source :: remaining) realRequest imaginaryRequest)).value =
      .ok (originalReply source (half realRequest)
        (half imaginaryRequest) question) := rfl

/-- The tail handler returns the exact original remaining path's reply. -/
theorem tailHandler_original (source : PolynomialSegment) (remaining : Source.PolynomialPath)
    (realRequest imaginaryRequest : AccuracyRequest)
    (question : Query remaining (half realRequest) (half imaginaryRequest)) :
    ((tailHandler source remaining realRequest imaginaryRequest question).protocol.run
      (pathReply (source :: remaining) realRequest imaginaryRequest)).value =
      .ok (pathReply remaining (half realRequest) (half imaginaryRequest) question) := rfl

/-- Original real-source execution produces the original ordered path request. -/
theorem realComputation_original : ∀ (source : Source.PolynomialPath) (state : RealState source)
    (realRequest imaginaryRequest : AccuracyRequest),
    ((realComputation source state realRequest imaginaryRequest).protocol.run
      (pathReply source realRequest imaginaryRequest)).value =
      .ok ((boundProcess source).request state realRequest.tolerance realRequest.positive)
  | [], state, _, _ => by cases state; rfl
  | source :: remaining, state, realRequest, imaginaryRequest => by
      have headOriginal := Program.substituteChecked_value
        (headHandler source remaining realRequest imaginaryRequest)
        (realConstruction source state.1 (half realRequest) (half imaginaryRequest))
        (pathReply (source :: remaining) realRequest imaginaryRequest)
        (originalReply source (half realRequest) (half imaginaryRequest))
        (headHandler_original source remaining realRequest imaginaryRequest)
      have tailOriginal := Program.substituteChecked_value
        (tailHandler source remaining realRequest imaginaryRequest)
        (realComputation remaining state.2 (half realRequest) (half imaginaryRequest))
        (pathReply (source :: remaining) realRequest imaginaryRequest)
        (pathReply remaining (half realRequest) (half imaginaryRequest))
        (tailHandler_original source remaining realRequest imaginaryRequest)
      have innerOriginal : ((Continuation.historyComputation
          (realModulus source) state.1 (half realRequest)).protocol.run
          (Continuation.originalReplyAll (realPreparation source
            (half realRequest)))).value =
          .ok ((Rational.Continuous.integrationProcess (Partition.Continuous.projected source)).request
            state.1 (half realRequest).tolerance (half realRequest).positive) :=
        Continuation.historyComputation_original
          (realModulus source) state.1 (half realRequest)
      unfold realComputation
      rw [Program.bind_execution, Protocol.bind_run_value, headOriginal]
      dsimp only
      rw [realConstruction_original]
      dsimp only
      rw [innerOriginal]
      rw [Program.map_execution, Protocol.map_run_value, tailOriginal]
      dsimp only
      rw [realComputation_original remaining state.2 (half realRequest) (half imaginaryRequest)]
      rfl

/-- Original imaginary-source execution produces the original ordered path request. -/
theorem imaginaryComputation_original : ∀ (source : Source.PolynomialPath) (state : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest),
    ((imaginaryComputation source state realRequest imaginaryRequest).protocol.run
      (pathReply source realRequest imaginaryRequest)).value =
      .ok ((imaginaryBoundProcess source).request state imaginaryRequest.tolerance imaginaryRequest.positive)
  | [], state, _, _ => by cases state; rfl
  | source :: remaining, state, realRequest, imaginaryRequest => by
      have headOriginal := Program.substituteChecked_value
        (headHandler source remaining realRequest imaginaryRequest)
        (imaginaryConstruction source state.1
          (half realRequest) (half imaginaryRequest))
        (pathReply (source :: remaining) realRequest imaginaryRequest)
        (originalReply source (half realRequest) (half imaginaryRequest))
        (headHandler_original source remaining realRequest imaginaryRequest)
      have tailOriginal := Program.substituteChecked_value
        (tailHandler source remaining realRequest imaginaryRequest)
        (imaginaryComputation remaining state.2 (half realRequest) (half imaginaryRequest))
        (pathReply (source :: remaining) realRequest imaginaryRequest)
        (pathReply remaining (half realRequest) (half imaginaryRequest))
        (tailHandler_original source remaining realRequest imaginaryRequest)
      have innerOriginal : ((Continuation.historyComputation
          (imaginaryModulus source) state.1 (half imaginaryRequest)).protocol.run
          (Continuation.originalReplyAll (imaginaryPreparation source
            (half imaginaryRequest)))).value =
          .ok ((Rational.Continuous.integrationProcess (Partition.Continuous.projectedIm source)).request
            state.1 (half imaginaryRequest).tolerance (half imaginaryRequest).positive) :=
        Continuation.historyComputation_original
          (imaginaryModulus source) state.1 (half imaginaryRequest)
      unfold imaginaryComputation
      rw [Program.bind_execution, Protocol.bind_run_value, headOriginal]
      dsimp only
      rw [imaginaryConstruction_original]
      dsimp only
      rw [innerOriginal]
      rw [Program.map_execution, Protocol.map_run_value, tailOriginal]
      dsimp only
      rw [imaginaryComputation_original remaining state.2 (half realRequest) (half imaginaryRequest)]
      rfl

/-- Original execution returns both original ordered path requests and their complete outer trace. -/
theorem computation_original (source : Source.PolynomialPath) (real : RealState source)
    (imaginary : ImaginaryState source) (realRequest imaginaryRequest : AccuracyRequest) :
    ((computation source real imaginary realRequest imaginaryRequest).protocol.run
      (pathReply source realRequest imaginaryRequest)).value =
      .ok ((boundProcess source).request real realRequest.tolerance realRequest.positive,
        (imaginaryBoundProcess source).request imaginary imaginaryRequest.tolerance imaginaryRequest.positive) := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, realComputation_original]
  rw [Program.map_execution, Protocol.map_run_value, imaginaryComputation_original]
  rfl

/-- Replay returns both original continued path states using only the recorded source replies. -/
theorem computation_replay (source : Source.PolynomialPath) (real : RealState source)
    (imaginary : ImaginaryState source) (realRequest imaginaryRequest : AccuracyRequest) :
    let program := computation source real imaginary realRequest imaginaryRequest
    let oracle := pathReply source realRequest imaginaryRequest
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok ((boundProcess source).request real realRequest.tolerance realRequest.positive,
        (imaginaryBoundProcess source).request imaginary imaginaryRequest.tolerance imaginaryRequest.positive)) := by
  let program := computation source real imaginary realRequest imaginaryRequest
  let oracle := pathReply source realRequest imaginaryRequest
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Changing replies outside the observed path trace preserves the complete original execution. -/
theorem payload_erasure (source : Source.PolynomialPath) (real : RealState source)
    (imaginary : ImaginaryState source) (realRequest imaginaryRequest : AccuracyRequest)
    {Payload : Type} (payload : Payload)
    (outside : Payload → Query source realRequest imaginaryRequest → Reply source) :
    let program := computation source real imaginary realRequest imaginaryRequest
    let oracle := pathReply source realRequest imaginaryRequest
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation source real imaginary realRequest imaginaryRequest).protocol.annotation_erasure
    (pathReply source realRequest imaginaryRequest) payload outside

/-- Both returned path enclosures contain the same retained original compiled sample.

The compilation is supplied by its original source owner, and both coordinate
states are the actual results of the ordered source requests. -/
theorem compiled_coordinates_contained {source : Source.PolynomialPath}
    (compiled : Compiled.CompiledPartition source) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    let realState := (boundProcess source).request real realRequest.tolerance realRequest.positive
    let imaginaryState := (imaginaryBoundProcess source).request imaginary imaginaryRequest.tolerance
      imaginaryRequest.positive
    ((boundProcess source).bound realState).Contains compiled.sample.re ∧
      ((imaginaryBoundProcess source).bound imaginaryState).Contains compiled.sample.im := by
  rw [compiled.sample_eq]
  exact sample_coordinates_contained compiled.cells _ _

/-- The returned path midpoints have a squared-error bound for that retained compiled sample. -/
theorem compiled_midpoint_normSq_le {source : Source.PolynomialPath}
    (compiled : Compiled.CompiledPartition source) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    let realState := (boundProcess source).request real realRequest.tolerance realRequest.positive
    let imaginaryState := (imaginaryBoundProcess source).request imaginary imaginaryRequest.tolerance
      imaginaryRequest.positive
    Norm.Basic.normSq (compiled.sample - midpoint source realState imaginaryState) ≤
      (((boundProcess source).bound realState).width * (1 / 2)) ^ 2 +
      (((imaginaryBoundProcess source).bound imaginaryState).width * (1 / 2)) ^ 2 := by
  rw [compiled.sample_eq]
  exact sample_midpoint_normSq_le compiled.cells _ _

end Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation

end
