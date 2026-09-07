import FTA.CCLPositiveEventSemantics
import FTA.CCLEventExtraction

/-!
# History-free event-owner traversal

The direct x--y controller reads only the genuinely new predicate introduced
by the next raw bit.  This module traverses the existing finite global and
terminal-guard event families using their incremental canonical truth tables.
The local child predicates are algebraically exclusive, so the traversal
returns one owner bit or exact all-`neither` certificates without consulting
historical parser constraints or a compatible sample.
-/

namespace FTA
namespace CCLIncrementalEventOwner

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLBranchPlan
open FTA.CCLGeometry
open FTA.CCLEventExtraction
open FTA.CCLPositiveEventSemantics
open FTA.CentralBandGrid
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial CCL.GaussianRat

/-- Finite direct-owner decision for globally generated event cells. -/
inductive EventFamilyDecision
    {p : GaussianPolynomial} {box : RatBox} {state : RawParser.State} :
    (candidates : List (SourceInputEventCell p box state)) → Type where
  | owner {candidates : List (SourceInputEventCell p box state)}
      (candidate : SourceInputEventCell p box state)
      (member : candidate ∈ candidates) (bit : Bool)
      (checks : inputEventIncrementalChecks candidate.inputCell =
        ownerPair bit) : EventFamilyDecision candidates
  | allNeither {candidates : List (SourceInputEventCell p box state)}
      (none : ∀ candidate ∈ candidates,
        inputEventIncrementalChecks candidate.inputCell = (false, false)) :
      EventFamilyDecision candidates

/-- Select the first global event owned by one history-free child. -/
def decideEventFamily
    {p : GaussianPolynomial} {box : RatBox} {state : RawParser.State} :
    (candidates : List (SourceInputEventCell p box state)) →
      EventFamilyDecision candidates
  | [] => .allNeither (by simp)
  | candidate :: candidates => by
      cases falseCheck :
          (inputEventIncrementalChecks candidate.inputCell).1 with
      | false =>
          cases trueCheck :
              (inputEventIncrementalChecks candidate.inputCell).2 with
          | false =>
              exact match decideEventFamily candidates with
              | .owner selected member bit checks =>
                  .owner selected (by simp [member]) bit checks
              | .allNeither allNone =>
                  .allNeither (by
                    intro selected member
                    rcases List.mem_cons.mp member with rfl | tailMember
                    · exact Prod.ext falseCheck trueCheck
                    · exact allNone selected tailMember)
          | true =>
              exact .owner candidate (by simp) true
                (Prod.ext falseCheck trueCheck)
      | true =>
          cases trueCheck :
              (inputEventIncrementalChecks candidate.inputCell).2 with
          | false =>
              exact .owner candidate (by simp) false
                (Prod.ext falseCheck trueCheck)
          | true =>
              exact (inputEventIncrementalChecks_ne_both candidate.inputCell
                (Prod.ext falseCheck trueCheck)).elim

/-- Selected global direct owner with its exact source count. -/
structure SelectedEvent
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) where
  candidate : SourceInputEventCell p output.state.box state
  member : candidate ∈ separatedInputEventCells p state output
  bit : Bool
  checks : inputEventIncrementalChecks candidate.inputCell = ownerPair bit
  decision : CurveEventCountDecision p
    candidate.sourceEvent.partition.entry.chart.path output.state.box
    candidate.sourceEvent.event

/-- Owner traversal for the finite global family of a separated state. -/
def decideSeparatedEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    Option (SelectedEvent output) :=
  match decideEventFamily (separatedInputEventCells p state output) with
  | .owner candidate member bit checks =>
      some
        { candidate := candidate
          member := member
          bit := bit
          checks := checks
          decision := candidate.decideSourceCount member }
  | .allNeither _ => none

/-! ## Terminal-guard event family -/

inductive GuardFamilyDecision
    {p : GaussianPolynomial} {box : RatBox} {state : RawParser.State} :
    (candidates : List (SourceGuardInputEventCell p box state)) → Type where
  | owner {candidates : List (SourceGuardInputEventCell p box state)}
      (candidate : SourceGuardInputEventCell p box state)
      (member : candidate ∈ candidates) (bit : Bool)
      (checks : inputEventIncrementalChecks candidate.inputCell =
        ownerPair bit) : GuardFamilyDecision candidates
  | allNeither {candidates : List (SourceGuardInputEventCell p box state)}
      (none : ∀ candidate ∈ candidates,
        inputEventIncrementalChecks candidate.inputCell = (false, false)) :
      GuardFamilyDecision candidates

def decideGuardFamily
    {p : GaussianPolynomial} {box : RatBox} {state : RawParser.State} :
    (candidates : List (SourceGuardInputEventCell p box state)) →
      GuardFamilyDecision candidates
  | [] => .allNeither (by simp)
  | candidate :: candidates => by
      cases falseCheck :
          (inputEventIncrementalChecks candidate.inputCell).1 with
      | false =>
          cases trueCheck :
              (inputEventIncrementalChecks candidate.inputCell).2 with
          | false =>
              exact match decideGuardFamily candidates with
              | .owner selected member bit checks =>
                  .owner selected (by simp [member]) bit checks
              | .allNeither allNone =>
                  .allNeither (by
                    intro selected member
                    rcases List.mem_cons.mp member with rfl | tailMember
                    · exact Prod.ext falseCheck trueCheck
                    · exact allNone selected tailMember)
          | true =>
              exact .owner candidate (by simp) true
                (Prod.ext falseCheck trueCheck)
      | true =>
          cases trueCheck :
              (inputEventIncrementalChecks candidate.inputCell).2 with
          | false =>
              exact .owner candidate (by simp) false
                (Prod.ext falseCheck trueCheck)
          | true =>
              exact (inputEventIncrementalChecks_ne_both candidate.inputCell
                (Prod.ext falseCheck trueCheck)).elim

structure SelectedGuardEvent
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) where
  candidate : SourceGuardInputEventCell p output.state.box state
  member : candidate ∈ separatedGuardInputEventCells p state output
  bit : Bool
  checks : inputEventIncrementalChecks candidate.inputCell = ownerPair bit
  decision : CurveEventCountDecision p
    candidate.sourceEvent.sourceCell.partition.entry.chart.path
    output.state.box candidate.sourceEvent.event

def decideSeparatedGuardEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    Option (SelectedGuardEvent output) :=
  match decideGuardFamily
      (separatedGuardInputEventCells p state output) with
  | .owner candidate member bit checks =>
      some
        { candidate := candidate
          member := member
          bit := bit
          checks := checks
          decision := candidate.decideSourceCount }
  | .allNeither _ => none

/-! ## Common geometry payload and combined traversal -/

/-- Geometry-facing direct owner, independent of global/guard provenance.
This is the shared incremental geometry payload used by complete owners too. -/
abbrev SelectedPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) := IncrementalEventPayload output

/-- The bit retained by a direct payload is true in the event's history-free
canonical oracle. -/
theorem SelectedPayload.selectedCanonical_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedPayload output) :
    formulaEvalWith
      (CCLFormulaPullback.inputIncrementalAdvanceFormula state selected.bit)
      (inputEventCanonicalValue selected.candidate.inputCell) = true := by
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.fst selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair] using
        component
  | true =>
      have component := congrArg Prod.snd selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair] using
        component

/-- The opposite incremental child is false at the same canonical event. -/
theorem SelectedPayload.otherCanonical_fails
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedPayload output) :
    formulaEvalWith
      (CCLFormulaPullback.inputIncrementalAdvanceFormula state
        (!selected.bit))
      (inputEventCanonicalValue selected.candidate.inputCell) = false := by
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.snd selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair,
        Bool.not_false] using component
  | true =>
      have component := congrArg Prod.fst selected.checks
      simpa only [inputEventIncrementalChecks, bitEq, ownerPair,
        Bool.not_true] using component

/-- Winding-one Newton band extracted from a positive direct owner.  Its
geometry depends only on the isolated event cell, not on historical owner
formulas. -/
def SelectedPayload.numericalState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient
    selected.candidate.inputCell squarefree output.state.clearance elimination

theorem SelectedPayload.numericalState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} (selected : SelectedPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior (selected.numericalState squarefree elimination).box
      output.state.box :=
  eventWindingOneState_strictInterior output.state.refinesAmbient
    selected.candidate.inputCell squarefree output.state.clearance elimination

def SelectedEvent.toPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEvent output) : SelectedPayload output where
  candidate := .global selected.candidate
  bit := selected.bit
  checks := selected.checks
  decision := selected.decision
  sourceMember := selected.candidate.source_mem_inputPlan selected.member

def SelectedGuardEvent.toPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEvent output) : SelectedPayload output where
  candidate := .guarded selected.candidate
  bit := selected.bit
  checks := selected.checks
  decision := selected.decision
  sourceMember := selected.candidate.source_mem_inputPlan selected.member

inductive CombinedDecision
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) where
  | globalOwner (selected : SelectedEvent output)
  | guardOwner (selected : SelectedGuardEvent output)
  | allNeither
      (globalNone : ∀ candidate ∈ separatedInputEventCells p state output,
        inputEventIncrementalChecks candidate.inputCell = (false, false))
      (guardNone : ∀ candidate ∈
        separatedGuardInputEventCells p state output,
        inputEventIncrementalChecks candidate.inputCell = (false, false))

/-- Traverse both event representations, preferring the global family. -/
def decideCombined
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) : CombinedDecision output :=
  match decideEventFamily (separatedInputEventCells p state output) with
  | .owner candidate member bit checks =>
      .globalOwner
        { candidate := candidate
          member := member
          bit := bit
          checks := checks
          decision := candidate.decideSourceCount member }
  | .allNeither globalNone =>
      match decideGuardFamily
          (separatedGuardInputEventCells p state output) with
      | .owner candidate member bit checks =>
          .guardOwner
            { candidate := candidate
              member := member
              bit := bit
              checks := checks
              decision := candidate.decideSourceCount }
      | .allNeither guardNone =>
          .allNeither globalNone guardNone

end CCLIncrementalEventOwner
end FTA
