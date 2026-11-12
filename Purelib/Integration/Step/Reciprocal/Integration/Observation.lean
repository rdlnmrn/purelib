module
public import Purelib.Integration.Step.Reciprocal.Integration
public import Purelib.Integration.Cell.Source.Exceptional.Observation
public import Purelib.Integration.Cell.Source.Initial.Observation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing reciprocal-step integration

The original positive request fixes its finite reciprocal cutoff, exceptional
preparation and target source. The displayed ordered calls include the actual
truncated-source observations and the original-source reads on the marked
initial tail. Returned points construct the same complete reciprocal result.
-/

public section

namespace Purelib.Integration.Step.Reciprocal.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.SourceFrontier

/-- The selected exceptional preparation of the original finite reciprocal truncation. -/
@[expose] def preparation (request : AccuracyRequest) :=
  SourceFrontier.Exceptional.Preparation.prepare (auxiliaryModulus request) (quarterRequest request)

/-- An original truncated-mesh occurrence or a target-source rational tail tag. -/
abbrev Query (request : AccuracyRequest) :=
  Sum (SourceFrontier.Observation.Entry (preparation request).partition) Fraction.Rational

/-- A reply retains whether it came from the truncated or original reciprocal source. -/
abbrev Reply (request : AccuracyRequest) :=
  Sum (SourcePoint (truncated (tailCount request.tolerance))) (SourcePoint value)

set_option genInjectivity false in
/-- An invalid operation or point reply during the original reciprocal construction. -/
inductive Failure (request : AccuracyRequest) where
  /-- The reply belongs to the other original source operation. -/ | operation (requested : Query request)
  /-- A truncated-source reply has the wrong original mesh tag. -/ | auxiliary
      (invalid : SourceFrontier.Observation.InvalidTag (preparation request).partition)
  /-- A target-source reply has the wrong marked-tail tag. -/ | tail
      (invalid : Initial.Observation.InvalidTag)

constructive_injectivity Failure

/-- The original two source owners answer their own displayed requests. -/
@[expose] def originalReply (request : AccuracyRequest) : Query request → Reply request :=
  let count := tailCount request.tolerance
  let source := truncated count
  fun
  | .inl entry => .inl (SourceFrontier.Observation.originalReply source (preparation request).partition entry)
  | .inr point => .inr (Initial.Observation.originalReply value point)

/-- Display one original truncated-source point request. -/
@[expose] def auxiliaryHandler (request : AccuracyRequest)
    (entry : SourceFrontier.Observation.Entry (preparation request).partition) :
    Program (Query request) (Reply request)
      (Except (Failure request) (SourcePoint (truncated (tailCount request.tolerance)))) :=
  .request (.inl entry) fun reply => match reply with
    | .inl point => .pure (.ok point)
    | .inr _ => .pure (.error (.operation (.inl entry)))

/-- Compose the original exceptional truncation with its displayed source requests. -/
@[expose] def auxiliaryProgram (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    Program (Query request) (Reply request) (Except (Failure request)
      (Basic.Execution (SourceFrontier.Observation.Entry (preparation request).partition)
        (SourcePoint (truncated (tailCount request.tolerance)))
        (Except (SourceFrontier.Observation.InvalidTag (preparation request).partition)
          (Exceptional.Observation.CertifiedResult (auxiliaryModulus request)
            (auxiliaryCachedReadings request cached) (quarterRequest request))))) :=
  (Exceptional.Observation.computation (auxiliaryModulus request)
    (auxiliaryCachedReadings request cached) (quarterRequest request)).substituteChecked (auxiliaryHandler request)

/-- Original execution retains the complete original truncated-source execution. -/
theorem auxiliaryProgram_original (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    ((auxiliaryProgram cached request).protocol.run (originalReply request)).value =
      .ok ((Exceptional.Observation.computation (auxiliaryModulus request)
        (auxiliaryCachedReadings request cached) (quarterRequest request)).protocol.run
          (SourceFrontier.Observation.originalReply (truncated (tailCount request.tolerance))
            (preparation request).partition)) := by
  unfold auxiliaryProgram
  apply Program.substituteChecked_value
  intro entry
  rfl

/-- Display one original target-source point request on the marked initial tail. -/
@[expose] def tailHandler (request : AccuracyRequest) (point : Fraction.Rational) :
    Program (Query request) (Reply request) (Except (Failure request) (SourcePoint value)) :=
  .request (.inr point) fun reply => match reply with
    | .inl _ => .pure (.error (.operation (.inr point)))
    | .inr point => .pure (.ok point)

/-- The original target source lies in its retained unit range. -/
theorem bounded (point : Fraction.Rational) (_lower : 0 ≤ point) (_upper : point ≤ 1) :
    unitRange.Contains (value point) := unitRange_contains point

/-- Compose target-source replacement with its actual marked-tail requests. -/
@[expose] def tailProgram (cached : List (SourcePoint value)) (request : AccuracyRequest)
    (auxiliary : SourceFrontier.Exceptional.Result (auxiliaryModulus request)) :
    Program (Query request) (Reply request) (Except (Failure request)
      (Basic.Execution Fraction.Rational (SourcePoint value)
        (Except Initial.Observation.InvalidTag
          (Initial.Observation.CertifiedFrontier cached auxiliary.frontier
            (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded)))) :=
  (Initial.Observation.computation cached auxiliary.frontier
    (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded).substituteChecked
      (tailHandler request)

/-- Original execution retains the complete original target-source replacement execution. -/
theorem tailProgram_original (cached : List (SourcePoint value)) (request : AccuracyRequest)
    (auxiliary : SourceFrontier.Exceptional.Result (auxiliaryModulus request)) :
    ((tailProgram cached request auxiliary).protocol.run (originalReply request)).value =
      .ok ((Initial.Observation.computation cached auxiliary.frontier
        (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded).protocol.run
          (Initial.Observation.originalReply value)) := by
  unfold tailProgram
  apply Program.substituteChecked_value
  intro point
  rfl

/-- Assemble the original reciprocal result from returned truncated and target-source frontiers. -/
@[expose] def assemble (cached : List (SourcePoint value)) (request : AccuracyRequest)
    (auxiliary : Exceptional.Observation.CertifiedResult (auxiliaryModulus request)
      (auxiliaryCachedReadings request cached) (quarterRequest request))
    (frontier : Initial.Observation.CertifiedFrontier cached auxiliary.val.frontier
      (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded) : Result := by
  have auxiliary_eq : auxiliary.val = auxiliaryResult request := auxiliary.property.trans
    (SourceFrontier.Exceptional.buildCached_eq (auxiliaryModulus request)
      (auxiliaryCachedReadings request cached) (quarterRequest request))
  have frontier_eq : frontier.val = SourceFrontier.Initial.replace auxiliary.val.frontier
      (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded :=
    frontier.property.trans (SourceFrontier.Initial.replaceCached_eq cached auxiliary.val.frontier
      (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded)
  have accurate : (integralBound frontier.val.cells).width < request.tolerance := by
    rw [frontier_eq, auxiliary_eq]
    exact frontier_width_lt request
  exact ⟨request, auxiliary.val, auxiliary_eq, frontier.val, frontier_eq, accurate⟩

/-- Returned source frontiers assemble into the exact original cache-aware reciprocal result. -/
theorem assemble_eq (cached : List (SourcePoint value)) (request : AccuracyRequest)
    (auxiliary : Exceptional.Observation.CertifiedResult (auxiliaryModulus request)
      (auxiliaryCachedReadings request cached) (quarterRequest request))
    (frontier : Initial.Observation.CertifiedFrontier cached auxiliary.val.frontier
      (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request) bounded) :
    assemble cached request auxiliary frontier = buildCached cached request := by
  cases auxiliary with
  | mk auxiliary auxiliary_eq =>
    cases auxiliary_eq
    cases frontier with
    | mk frontier frontier_eq =>
      cases frontier_eq
      rfl

/-- A complete reciprocal result certified as the original cache-aware construction. -/
abbrev CertifiedResult (cached : List (SourcePoint value)) (request : AccuracyRequest) :=
  {result : Result // result = buildCached cached request}

/-- The complete auxiliary observation execution for an original reciprocal request. -/
abbrev AuxiliaryExecution (cached : List (SourcePoint value)) (request : AccuracyRequest) :=
  Basic.Execution (SourceFrontier.Observation.Entry (preparation request).partition)
    (SourcePoint (truncated (tailCount request.tolerance)))
    (Except (SourceFrontier.Observation.InvalidTag (preparation request).partition)
      (Exceptional.Observation.CertifiedResult (auxiliaryModulus request)
        (auxiliaryCachedReadings request cached) (quarterRequest request)))

/-- Finish an auxiliary execution using its retained original tail endpoint.

The endpoint equality identifies the supplied value with the request's
selected tail. The returned auxiliary frontier and target readings assemble
the original cache-aware reciprocal result. -/
@[expose] def finish (cached : List (SourcePoint value)) (request : AccuracyRequest)
    (endpoint : Fraction.Rational) (endpointEq : endpoint = 1 / (tailCount request.tolerance : Fraction.Rational))
    (result : Except (Failure request) (AuxiliaryExecution cached request)) :
    Program (Query request) (Reply request) (Except (Failure request) (CertifiedResult cached request)) :=
  match result with
  | .error invalid => .pure (.error invalid)
  | .ok execution =>
      match execution.value with
      | .error invalid => .pure (.error (.auxiliary invalid))
      | .ok auxiliary =>
          let sameTail : ∀ point, endpoint < point → value point = truncated (tailCount request.tolerance) point :=
            fun point above => agreement request point (endpointEq ▸ above)
          let tail := Initial.Observation.computation cached auxiliary.val.frontier endpoint unitRange sameTail bounded
          (tail.substituteChecked (tailHandler request)).map fun result =>
              match result with
              | .error invalid => .error invalid
              | .ok execution =>
                  match execution.value with
                  | .error invalid => .error (.tail invalid)
                  | .ok frontier =>
                      have sameFrontier : Initial.Observation.CertifiedFrontier cached auxiliary.val.frontier
                          endpoint unitRange sameTail bounded =
                          Initial.Observation.CertifiedFrontier cached auxiliary.val.frontier
                            (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange
                            (agreement request) bounded := by
                        cases endpointEq
                        rfl
                      let original := cast sameFrontier frontier
                      .ok ⟨assemble cached request auxiliary original,
                        assemble_eq cached request auxiliary original⟩

/-- Observe the original finite truncation and marked-tail source replacement in their actual order. -/
@[expose] def computation (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    Program (Query request) (Reply request) (Except (Failure request) (CertifiedResult cached request)) :=
  let count := tailCount request.tolerance
  let endpoint := 1 / (count : Fraction.Rational)
  let modulus := truncatedModulus count (tailCount_ge_two request.tolerance)
  let readings := auxiliaryCachedReadingsAt count endpoint rfl cached
  let auxiliary := (Exceptional.Observation.computation modulus readings (quarterRequest request)).substituteChecked
    (auxiliaryHandler request)
  auxiliary.bind (finish cached request endpoint rfl)

/-- Original-source execution returns the complete cache-aware reciprocal result. -/
theorem computation_original (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    ((computation cached request).protocol.run (originalReply request)).value =
      .ok ⟨buildCached cached request, rfl⟩ := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value]
  let finishValue := fun result : Except (Failure request) (AuxiliaryExecution cached request) =>
    ((finish cached request (1 / (tailCount request.tolerance : Fraction.Rational)) rfl result).protocol.run
      (originalReply request)).value
  have auxiliaryOriginal := auxiliaryProgram_original cached request
  apply (congrArg finishValue auxiliaryOriginal).trans
  dsimp only [finishValue]
  unfold finish
  dsimp only [preparation]
  rw [Exceptional.Observation.computation_original]
  have tailOriginal (auxiliary : SourceFrontier.Exceptional.Result (auxiliaryModulus request)) :=
    tailProgram_original cached request auxiliary
  unfold tailProgram at tailOriginal
  rw [Program.map_execution, Protocol.map_run_value, tailOriginal]
  dsimp only
  rw [Initial.Observation.computation_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assemble_eq cached request _ _

/-- Exact replay recovers the complete reciprocal result without repeating either displayed source request. -/
theorem computation_replay (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    (computation cached request).protocol.replayExact
      ((computation cached request).protocol.run (originalReply request)).trace =
        .ok (.ok ⟨buildCached cached request, rfl⟩) := by
  rw [(computation cached request).protocol.replayExact_run, computation_original]

/-- Replies outside the executed reciprocal-source trace preserve the complete result and ordered trace. -/
theorem payload_erasure (cached : List (SourcePoint value)) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload) (outside : Payload → Query request → Reply request) :
    (computation cached request).protocol.run (Boundary.Trace.overlay
      ((computation cached request).protocol.run (originalReply request)).trace (outside payload)) =
      (computation cached request).protocol.run (originalReply request) :=
  (computation cached request).protocol.annotation_erasure (originalReply request) payload outside

end Purelib.Integration.Step.Reciprocal.Observation

end
