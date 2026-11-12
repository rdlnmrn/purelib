module
public import Purelib.Integration.Cell.Numerical.Common.Observation.Independent
public import Purelib.Integration.Cell.Numerical.Continuous.Observation.Continuation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Composing numerical histories and joint comparison

Each request first advances its own retained numerical history. Common point
acquisition and joint admission then consume the two actual returned states.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Observation.Independent.History

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.NumericalFrontier.Continuous.Observation

variable {leftSource rightSource : Fraction.Rational → BoundProcess}
variable (leftModulus : Rational.Uniform.Numerical leftSource)
variable (rightModulus : Rational.Uniform.Numerical rightSource)
variable (leftState : (producer leftModulus).integrationProcess.State)
variable (rightState : (producer rightModulus).integrationProcess.State)
variable (leftRequest rightRequest pointRequest budget : AccuracyRequest)

/-- A joint request retains the actual returned certified histories and their common question. -/
abbrev JointQuery :=
  Σ left : Continuation.CertifiedState leftModulus leftState leftRequest,
    Σ right : Continuation.CertifiedState rightModulus rightState rightRequest,
      Joint.Query left.val.1 right.val.1 pointRequest

/-- Certified owners are unique, so only the original joint question needs a comparison. -/
instance : DecidableEq
    (JointQuery leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest) := by
  intro first second
  cases first with
  | mk firstLeft firstTail =>
    cases firstTail with
    | mk firstRight firstQuestion =>
      cases second with
      | mk secondLeft secondTail =>
        cases secondTail with
        | mk secondRight secondQuestion =>
          have leftEq : firstLeft = secondLeft := Subtype.ext (firstLeft.property.trans secondLeft.property.symm)
          have rightEq : firstRight = secondRight := Subtype.ext (firstRight.property.trans secondRight.property.symm)
          cases leftEq
          cases rightEq
          by_cases same : firstQuestion = secondQuestion
          · cases same
            exact isTrue rfl
          · exact isFalse (fun equal => same (by cases equal; rfl))

/-- History requests precede the comparison request carrying both actual returned histories. -/
abbrev Query :=
  Sum (Continuation.Query (Preparation.prepare leftModulus leftRequest))
    (Sum (Continuation.Query (Preparation.prepare rightModulus rightRequest))
      (JointQuery leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest))

/-- Displayed history and joint questions have executable equality. -/
instance [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    DecidableEq (Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest) := by
  intro first second
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      by_cases same : first = second
      · cases same
        exact isTrue rfl
      · exact isFalse (fun equal => same (by cases equal; rfl))
    | inr second => exact isFalse (fun equal => by cases equal)
  | inr first =>
    cases second with
    | inl second => exact isFalse (fun equal => by cases equal)
    | inr second =>
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          by_cases same : first = second
          · cases same
            exact isTrue rfl
          · exact isFalse (fun equal => same (by cases equal; rfl))
        | inr second => exact isFalse (fun equal => by cases equal)
      | inr first =>
        cases second with
        | inl second => exact isFalse (fun equal => by cases equal)
        | inr second =>
          by_cases same : first = second
          · cases same
            exact isTrue rfl
          · exact isFalse (fun equal => same (by cases equal; rfl))

variable (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
variable (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
variable (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)

/-- A joint reply retains the certified histories that own its point or joint observation. -/
abbrev JointReply :=
  Σ left : Continuation.CertifiedState leftModulus leftState leftRequest,
    Σ right : Continuation.CertifiedState rightModulus rightState rightRequest,
      Joint.Reply left.val.1 right.val.1 pointRequest budget equivalent leftCoherent rightCoherent

/-- Replies identify the history or joint operation and retain the original dependent owners. -/
abbrev Reply :=
  Sum (Continuation.Reply (Preparation.prepare leftModulus leftRequest)
    (Producer.effectiveBank leftState.1 ((producer leftModulus).retainedReadings leftState.2)) leftRequest)
    (Sum (Continuation.Reply (Preparation.prepare rightModulus rightRequest)
      (Producer.effectiveBank rightState.1 ((producer rightModulus).retainedReadings rightState.2)) rightRequest)
      (JointReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent))

/-- A complete comparison retains both actual returned histories as its original owners. -/
abbrev Result :=
  Σ left : Continuation.CertifiedState leftModulus leftState leftRequest,
    Σ right : Continuation.CertifiedState rightModulus rightState rightRequest,
      Joint.Result left.val.1 right.val.1 pointRequest budget

set_option genInjectivity false in
/-- A wrong operation or a typed failure from either history or the actual joint comparison. -/
inductive Failure where
  /-- A reply named a different displayed operation. -/ | operation
      (requested : Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
  /-- The first history rejected its observed reply. -/ | left
      (invalid : Continuation.Failure (Preparation.prepare leftModulus leftRequest))
  /-- The second history rejected its observed reply. -/ | right
      (invalid : Continuation.Failure (Preparation.prepare rightModulus rightRequest))
  /-- The joint comparison rejected a reply for its actual returned history owners. -/ | joint
      (left : Continuation.CertifiedState leftModulus leftState leftRequest)
      (right : Continuation.CertifiedState rightModulus rightState rightRequest)
      (invalid : Joint.Failure left.val.1 right.val.1 pointRequest)

constructive_injectivity Failure

/-- Each operation uses its own history and, for comparison, the returned certified states. -/
@[expose] def originalReply :
    Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest →
      Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent
  | .inl question => .inl (Continuation.originalReplyAll _ _ _ question)
  | .inr (.inl question) => .inr (.inl (Continuation.originalReplyAll _ _ _ question))
  | .inr (.inr ⟨left, right, question⟩) =>
      .inr (.inr ⟨left, right, Joint.originalReply left.val.1 right.val.1 pointRequest budget
        equivalent leftCoherent rightCoherent question⟩)

/-- Lift a left history question, rejecting replies for either other operation. -/
@[expose] def leftHandler
    (question : Continuation.Query (Preparation.prepare leftModulus leftRequest)) :
    Program (Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
      (Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)
      (Except (Failure leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
        (Continuation.Reply (Preparation.prepare leftModulus leftRequest)
          (Producer.effectiveBank leftState.1 ((producer leftModulus).retainedReadings leftState.2)) leftRequest)) :=
  .request (.inl question) fun answer => match answer with
    | .inl reply => .pure (.ok reply)
    | .inr _ => .pure (.error (.operation (.inl question)))

/-- Lift a right history question, rejecting replies for either other operation. -/
@[expose] def rightHandler
    (question : Continuation.Query (Preparation.prepare rightModulus rightRequest)) :
    Program (Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
      (Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)
      (Except (Failure leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
        (Continuation.Reply (Preparation.prepare rightModulus rightRequest)
          (Producer.effectiveBank rightState.1 ((producer rightModulus).retainedReadings rightState.2))
          rightRequest)) :=
  .request (.inr (.inl question)) fun answer => match answer with
    | .inr (.inl reply) => .pure (.ok reply)
    | _ => .pure (.error (.operation (.inr (.inl question))))

/-- Lift a joint question using the same histories returned by the two preceding requests. -/
@[expose] def jointHandler
    (left : Continuation.CertifiedState leftModulus leftState leftRequest)
    (right : Continuation.CertifiedState rightModulus rightState rightRequest)
    (question : Joint.Query left.val.1 right.val.1 pointRequest) :
    Program (Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
      (Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)
      (Except (Failure leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
        (Joint.Reply left.val.1 right.val.1 pointRequest budget equivalent leftCoherent rightCoherent)) :=
  .request (.inr (.inr ⟨left, right, question⟩)) fun answer => match answer with
    | .inr (.inr ⟨reportedLeft, reportedRight, reply⟩) => by
        have leftEq : reportedLeft = left := Subtype.ext (reportedLeft.property.trans left.property.symm)
        have rightEq : reportedRight = right := Subtype.ext (reportedRight.property.trans right.property.symm)
        cases leftEq
        cases rightEq
        exact .pure (.ok reply)
    | _ => .pure (.error (.operation (.inr (.inr ⟨left, right, question⟩))))

/-- Execute both original histories, then compare their exact returned frontiers. -/
@[expose] def computation [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    Program (Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
      (Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)
      (Except (Failure leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest)
        (Result leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget)) :=
  ((Continuation.certifiedHistoryComputation leftModulus leftState leftRequest).substituteChecked
    (leftHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
      equivalent leftCoherent rightCoherent)).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok execution => match execution.value with
      | .error invalid => .pure (.error (.left invalid))
      | .ok left =>
          ((Continuation.certifiedHistoryComputation rightModulus rightState rightRequest).substituteChecked
            (rightHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
              equivalent leftCoherent rightCoherent)).bind fun second =>
            match second with
            | .error invalid => .pure (.error invalid)
            | .ok execution => match execution.value with
              | .error invalid => .pure (.error (.right invalid))
              | .ok right =>
                  (Program.substituteChecked
                    (jointHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
                      budget equivalent leftCoherent rightCoherent left right)
                    (Joint.computation left.val.1 right.val.1 pointRequest budget equivalent
                      leftCoherent rightCoherent)).map
                        fun third =>
                    match third with
                    | .error invalid => .error invalid
                    | .ok execution => match execution.value with
                      | .error invalid => .error (.joint left right invalid)
                      | .ok result => .ok ⟨left, right, result⟩

/-- Original left replies recover the complete first history execution. -/
theorem leftProgram_original [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    (((Continuation.certifiedHistoryComputation leftModulus leftState leftRequest).substituteChecked
      (leftHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).protocol.run
      (originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).value =
      .ok ((Continuation.certifiedHistoryComputation leftModulus leftState leftRequest).protocol.run
        (Continuation.originalReplyAll (Preparation.prepare leftModulus leftRequest)
          (Producer.effectiveBank leftState.1 ((producer leftModulus).retainedReadings leftState.2)) leftRequest)) := by
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Original right replies recover the complete second history execution. -/
theorem rightProgram_original [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    (((Continuation.certifiedHistoryComputation rightModulus rightState rightRequest).substituteChecked
      (rightHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).protocol.run
      (originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).value =
      .ok ((Continuation.certifiedHistoryComputation rightModulus rightState rightRequest).protocol.run
        (Continuation.originalReplyAll (Preparation.prepare rightModulus rightRequest)
          (Producer.effectiveBank rightState.1 ((producer rightModulus).retainedReadings rightState.2))
          rightRequest)) := by
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Original joint replies recover the complete comparison at the actual returned histories. -/
theorem jointProgram_original [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)]
    (left : Continuation.CertifiedState leftModulus leftState leftRequest)
    (right : Continuation.CertifiedState rightModulus rightState rightRequest) :
    ((Program.substituteChecked
      (jointHandler leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent left right)
      (Joint.computation left.val.1 right.val.1 pointRequest budget equivalent leftCoherent rightCoherent)).protocol.run
      (originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).value =
      .ok ((Program.protocol
        (Joint.computation left.val.1 right.val.1 pointRequest budget equivalent leftCoherent rightCoherent)).run
          (Joint.originalReply left.val.1 right.val.1 pointRequest budget equivalent leftCoherent rightCoherent)) := by
  apply Program.substituteChecked_value
  intro question
  rfl

/-- The original certified result of the left persistent request. -/
abbrev originalLeft : Continuation.CertifiedState leftModulus leftState leftRequest :=
  ⟨(producer leftModulus).integrationProcess.request leftState leftRequest.tolerance leftRequest.positive, rfl⟩

/-- The original certified result of the right persistent request. -/
abbrev originalRight : Continuation.CertifiedState rightModulus rightState rightRequest :=
  ⟨(producer rightModulus).integrationProcess.request rightState rightRequest.tolerance rightRequest.positive, rfl⟩

/-- Original execution returns both complete requested histories and their original joint comparison. -/
theorem computation_original [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    ((computation leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
      equivalent leftCoherent rightCoherent).protocol.run
      (originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent)).value =
      .ok ⟨originalLeft leftModulus leftState leftRequest, originalRight rightModulus rightState rightRequest,
        let left := (originalLeft leftModulus leftState leftRequest).val.1
        let right := (originalRight rightModulus rightState rightRequest).val.1
        ⟨commonReadings left right pointRequest,
          requestJointReadings (commonReadings left right pointRequest) budget equivalent
            leftCoherent rightCoherent⟩⟩ := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, leftProgram_original]
  dsimp only
  rw [Continuation.certifiedHistoryComputation_original]
  rw [Program.bind_execution, Protocol.bind_run_value, rightProgram_original]
  dsimp only
  rw [Continuation.certifiedHistoryComputation_original]
  rw [Program.map_execution, Protocol.map_run_value, jointProgram_original]
  dsimp only
  rw [Joint.computation_original]

/-- Exact replay recovers the two original requested histories and their complete comparison. -/
theorem computation_replay [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)] :
    let program := computation leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
      budget equivalent leftCoherent rightCoherent
    let oracle := originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
      budget equivalent leftCoherent rightCoherent
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok ⟨originalLeft leftModulus leftState leftRequest, originalRight rightModulus rightState rightRequest,
        let left := (originalLeft leftModulus leftState leftRequest).val.1
        let right := (originalRight rightModulus rightState rightRequest).val.1
        ⟨commonReadings left right pointRequest,
          requestJointReadings (commonReadings left right pointRequest) budget equivalent
            leftCoherent rightCoherent⟩⟩) := by
  let program := computation leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
    budget equivalent leftCoherent rightCoherent
  let oracle := originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
    budget equivalent leftCoherent rightCoherent
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the combined trace preserve both returned histories and their complete comparison. -/
theorem payload_erasure [DecidableEq (NumericalPoint leftSource)] [DecidableEq (NumericalPoint rightSource)]
    {Payload : Type} (payload : Payload)
    (outside : Payload → Query leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest →
      Reply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent) :
    let program := computation leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
      budget equivalent leftCoherent rightCoherent
    let oracle := originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest
      budget equivalent leftCoherent rightCoherent
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
    equivalent leftCoherent rightCoherent).protocol.annotation_erasure
      (originalReply leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget
        equivalent leftCoherent rightCoherent) payload outside

/-- The returned joint readings bound answers inside the two actual returned frontier intervals. -/
theorem Result.answers_difference_le
    (result : Result leftModulus rightModulus leftState rightState leftRequest rightRequest pointRequest budget)
    (leftAnswer rightAnswer : Fraction.Rational)
    (leftInside : (integralBound result.1.val.1.cells).Contains leftAnswer)
    (rightInside : (integralBound result.2.1.val.1.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound result.1.val.1.cells).width + (integralBound result.2.1.val.1.cells).width +
        (pointRequest.tolerance + pointRequest.tolerance + budget.tolerance) :=
  result.2.2.2.answers_difference_le leftAnswer rightAnswer leftInside rightInside

end Purelib.Integration.NumericalFrontier.Common.Observation.Independent.History

end
