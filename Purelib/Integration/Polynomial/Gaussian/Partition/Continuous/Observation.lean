module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous
public import Purelib.Integration.Cell.Source.Continuous.Observation.Continuation
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Data.Rat.Interval.Bisection
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing both coordinates of an original polynomial segment

The original oriented segment supplies two rational polynomial sources. Each
coordinate request starts from its own saved integration history and consumes
the actual source replies used by the retained frontier construction. Both
returned enclosures admit the coordinates of the same compiled segment sample.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic
open Purelib.Integration.SourceFrontier.Continuous
open Purelib.Integration.SourceFrontier.Continuous.Observation

/-- The original real-coordinate source and its effective variation modulus. -/
abbrev realModulus (source : PolynomialSegment) := Dense.Rational.Bounds.Uniform.modulus (projected source)

/-- The original imaginary-coordinate source and its effective variation modulus. -/
abbrev imaginaryModulus (source : PolynomialSegment) := Dense.Rational.Bounds.Uniform.modulus (projectedIm source)

/-- A retained state of the original real-coordinate integration process. -/
abbrev RealState (source : PolynomialSegment) :=
  (Rational.Continuous.integrationProcess (projected source)).State

/-- A retained state of the original imaginary-coordinate integration process. -/
abbrev ImaginaryState (source : PolynomialSegment) :=
  (Rational.Continuous.integrationProcess (projectedIm source)).State

/-- The finite real-coordinate preparation for the supplied request. -/
@[expose] def realPreparation (source : PolynomialSegment) (request : AccuracyRequest) :
    Preparation (realModulus source) := Preparation.prepare (realModulus source) request

/-- The finite imaginary-coordinate preparation for the supplied request. -/
@[expose] def imaginaryPreparation (source : PolynomialSegment) (request : AccuracyRequest) :
    Preparation (imaginaryModulus source) := Preparation.prepare (imaginaryModulus source) request

/-- A source question retains which original coordinate and prepared occurrence it addresses. -/
abbrev Query (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest) :=
  Sum (Continuation.Query (realPreparation source realRequest))
    (Continuation.Query (imaginaryPreparation source imaginaryRequest))

/-- A source reply retains which original rational polynomial produced it. -/
abbrev Reply (source : PolynomialSegment) :=
  Sum (SourcePoint (projected source).eval) (SourcePoint (projectedIm source).eval)

set_option genInjectivity false in
/-- An observed coordinate request rejected the wrong source owner or an invalid original tag. -/
inductive Failure (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest) where
  /-- The returned reply belongs to the other original coordinate source. -/
  | owner (question : Query source realRequest imaginaryRequest)
  /-- The real-coordinate continuation identified its original invalid tag. -/
  | real (invalid : Continuation.Failure (realPreparation source realRequest))
  /-- The imaginary-coordinate continuation identified its original invalid tag. -/
  | imaginary (invalid : Continuation.Failure (imaginaryPreparation source imaginaryRequest))

constructive_injectivity Failure

/-- The actual two original polynomial sources answer their own displayed questions. -/
@[expose] def originalReply (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest) :
    Query source realRequest imaginaryRequest → Reply source
  | .inl question => .inl (Continuation.originalReplyAll (realPreparation source realRequest) question)
  | .inr question => .inr (Continuation.originalReplyAll (imaginaryPreparation source imaginaryRequest) question)

/-- Display one original real-coordinate source request and reject a reply from the other owner. -/
@[expose] def realHandler (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest)
    (question : Continuation.Query (realPreparation source realRequest)) :
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (SourcePoint (projected source).eval)) :=
  .request (.inl question) fun reply =>
    match reply with
    | .inl point => .pure (.ok point)
    | .inr _ => .pure (.error (.owner (.inl question)))

/-- Display one original imaginary-coordinate source request and reject a reply from the other owner. -/
@[expose] def imaginaryHandler (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest)
    (question : Continuation.Query (imaginaryPreparation source imaginaryRequest)) :
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (SourcePoint (projectedIm source).eval)) :=
  .request (.inr question) fun reply =>
    match reply with
    | .inl _ => .pure (.error (.owner (.inr question)))
    | .inr point => .pure (.ok point)

/-- Original execution of a real source handler returns the same original rational point. -/
theorem realHandler_original (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest)
    (question : Continuation.Query (realPreparation source realRequest)) :
    ((realHandler source realRequest imaginaryRequest question).protocol.run
      (originalReply source realRequest imaginaryRequest)).value =
      .ok (Continuation.originalReplyAll (realPreparation source realRequest) question) := rfl

/-- Original execution of an imaginary source handler returns the same original rational point. -/
theorem imaginaryHandler_original (source : PolynomialSegment) (realRequest imaginaryRequest : AccuracyRequest)
    (question : Continuation.Query (imaginaryPreparation source imaginaryRequest)) :
    ((imaginaryHandler source realRequest imaginaryRequest question).protocol.run
      (originalReply source realRequest imaginaryRequest)).value =
      .ok (Continuation.originalReplyAll (imaginaryPreparation source imaginaryRequest) question) := rfl

/-- Expand the original saved real-coordinate request through its actual rational source questions. -/
@[expose] def realConstruction (source : PolynomialSegment) (state : RealState source)
    (realRequest imaginaryRequest : AccuracyRequest) :=
  (Continuation.historyComputation (realModulus source) state realRequest).substituteChecked
    (realHandler source realRequest imaginaryRequest)

/-- Expand the original saved imaginary-coordinate request through its actual rational source questions. -/
@[expose] def imaginaryConstruction (source : PolynomialSegment) (state : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :=
  (Continuation.historyComputation (imaginaryModulus source) state imaginaryRequest).substituteChecked
    (imaginaryHandler source realRequest imaginaryRequest)

/-- Original expanded real execution retains its complete original result and ordered outer questions. -/
theorem realConstruction_original (source : PolynomialSegment) (state : RealState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    ((realConstruction source state realRequest imaginaryRequest).protocol.run
      (originalReply source realRequest imaginaryRequest)).value =
      .ok ((Continuation.historyComputation (realModulus source) state realRequest).protocol.run
        (Continuation.originalReplyAll (realPreparation source realRequest))) := by
  unfold realConstruction
  apply Program.substituteChecked_value
  exact realHandler_original source realRequest imaginaryRequest

/-- Original expanded imaginary execution retains its complete original result and ordered outer questions. -/
theorem imaginaryConstruction_original (source : PolynomialSegment) (state : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    ((imaginaryConstruction source state realRequest imaginaryRequest).protocol.run
      (originalReply source realRequest imaginaryRequest)).value =
      .ok ((Continuation.historyComputation (imaginaryModulus source) state imaginaryRequest).protocol.run
        (Continuation.originalReplyAll (imaginaryPreparation source imaginaryRequest))) := by
  unfold imaginaryConstruction
  apply Program.substituteChecked_value
  exact imaginaryHandler_original source realRequest imaginaryRequest

/-- Observe both original coordinate requests in order from their retained integration states.

The real continuation's returned state is retained before the imaginary
request begins. A wrong owner or an invalid tag stops the construction with
the actual finite obstruction and no later source request. -/
@[expose] def computation (source : PolynomialSegment) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    Program (Query source realRequest imaginaryRequest) (Reply source)
      (Except (Failure source realRequest imaginaryRequest) (RealState source × ImaginaryState source)) :=
  (realConstruction source real realRequest imaginaryRequest).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok execution =>
        match execution.value with
        | .error invalid => .pure (.error (.real invalid))
        | .ok realState =>
            (imaginaryConstruction source imaginary realRequest imaginaryRequest).map fun second =>
              match second with
              | .error invalid => .error invalid
              | .ok execution =>
                  match execution.value with
                  | .error invalid => .error (.imaginary invalid)
                  | .ok imaginaryState => .ok (realState, imaginaryState)

/-- Original execution returns the exact two original continued integration states. -/
theorem computation_original (source : PolynomialSegment) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    ((computation source real imaginary realRequest imaginaryRequest).protocol.run
      (originalReply source realRequest imaginaryRequest)).value =
      .ok ((Rational.Continuous.integrationProcess (projected source)).request
          real realRequest.tolerance realRequest.positive,
        (Rational.Continuous.integrationProcess (projectedIm source)).request
          imaginary imaginaryRequest.tolerance imaginaryRequest.positive) := by
  have realValue : ((Continuation.historyComputation (realModulus source) real realRequest).protocol.run
      (Continuation.originalReplyAll (realPreparation source realRequest))).value =
      .ok ((Rational.Continuous.integrationProcess (projected source)).request
        real realRequest.tolerance realRequest.positive) :=
    Continuation.historyComputation_original (realModulus source) real realRequest
  have imaginaryValue : ((Continuation.historyComputation
      (imaginaryModulus source) imaginary imaginaryRequest).protocol.run
      (Continuation.originalReplyAll (imaginaryPreparation source imaginaryRequest))).value =
      .ok ((Rational.Continuous.integrationProcess (projectedIm source)).request
        imaginary imaginaryRequest.tolerance imaginaryRequest.positive) :=
    Continuation.historyComputation_original (imaginaryModulus source) imaginary imaginaryRequest
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, realConstruction_original]
  dsimp only
  rw [realValue]
  rw [Program.map_execution, Protocol.map_run_value, imaginaryConstruction_original]
  dsimp only
  rw [imaginaryValue]

/-- Exact replay returns both original continued states without repeating either source's requests. -/
theorem computation_replay (source : PolynomialSegment) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) :
    let program := computation source real imaginary realRequest imaginaryRequest
    let oracle := originalReply source realRequest imaginaryRequest
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok ((Rational.Continuous.integrationProcess (projected source)).request
          real realRequest.tolerance realRequest.positive,
        (Rational.Continuous.integrationProcess (projectedIm source)).request
          imaginary imaginaryRequest.tolerance imaginaryRequest.positive)) := by
  let program := computation source real imaginary realRequest imaginaryRequest
  let oracle := originalReply source realRequest imaginaryRequest
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Changes outside the actual coordinate-source trace preserve both returned states and the complete ordered trace. -/
theorem payload_erasure (source : PolynomialSegment) (real : RealState source) (imaginary : ImaginaryState source)
    (realRequest imaginaryRequest : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query source realRequest imaginaryRequest → Reply source) :
    let program := computation source real imaginary realRequest imaginaryRequest
    let oracle := originalReply source realRequest imaginaryRequest
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation source real imaginary realRequest imaginaryRequest).protocol.annotation_erasure
    (originalReply source realRequest imaginaryRequest) payload outside

/-- Pair the actual real and imaginary midpoint readings of one original polynomial segment. -/
@[expose] def midpoint (source : PolynomialSegment) (real : RealState source) (imaginary : ImaginaryState source) :
    Basic.Canonical :=
  ⟨((Rational.Continuous.boundProcess (projected source)).bound real).midpoint,
    ((Rational.Continuous.boundProcess (projectedIm source)).bound imaginary).midpoint⟩

/-- Both saved coordinate states admit the coordinates of the same original compiled segment sample. -/
theorem sample_coordinates_contained {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (real : RealState source) (imaginary : ImaginaryState source) :
    ((Rational.Continuous.boundProcess (projected source)).bound real).Contains compiled.sample.re ∧
      ((Rational.Continuous.boundProcess (projectedIm source)).bound imaginary).Contains compiled.sample.im :=
  ⟨compiled_state_contains compiled real, compiled_im_state_contains compiled imaginary⟩

/-- The same original segment sample satisfies the squared half-width bound for the two retained coordinates. -/
theorem sample_midpoint_normSq_le {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (real : RealState source) (imaginary : ImaginaryState source) :
    Norm.Basic.normSq (compiled.sample - midpoint source real imaginary) ≤
      (((Rational.Continuous.boundProcess (projected source)).bound real).width * (1 / 2)) ^ 2 +
      (((Rational.Continuous.boundProcess (projectedIm source)).bound imaginary).width * (1 / 2)) ^ 2 := by
  exact Norm.Coordinates.sub_normSq_le compiled.sample (midpoint source real imaginary) _ _
    (Interval.abs_sub_midpoint_le (compiled_state_contains compiled real))
    (Interval.abs_sub_midpoint_le (compiled_im_state_contains compiled imaginary))

end Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation

end
