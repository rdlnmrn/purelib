module

public import Purelib.Integration.Cell.Numerical.Common.Observation.Independent
public import Purelib.Integration.Exponential.Real.Observation
public import Purelib.Integration.Exponential.Program.Source.Numerical
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual finite-Taylor and Gaussian numerical common points

The two original frontiers, selected finite depth and positive point request
are fixed. Exact finite-source misses and tagged Gaussian refinements are
displayed separately. Returned states and readings assemble the original
common occurrences without another source evaluation.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Common.Observation

/-- The exact finite Taylor source viewed as original point processes. -/
abbrev finiteProcess (depth : Nat) (point : Fraction.Rational) :=
  BoundProcess.exact (Horner.Real.finiteSource depth point)

/-- One exact finite-source query or tagged Gaussian process operation. -/
abbrev Query := Sum Fraction.Rational Real.Observation.Query

/-- One returned exact finite-source point or tagged Gaussian operation. -/
abbrev Reply (depth : Nat) := Sum (SourcePoint (Horner.Real.finiteSource depth)) Real.Observation.Reply

set_option genInjectivity false in
/-- A wrong common-source owner, finite-source tag or tagged Gaussian operation. -/
inductive Failure where
  /-- A reply belongs to the other original source owner. -/ | owner (requested : Query)
  /-- An exact finite-source reply belongs to a different rational tag. -/ | tag
      (requested reported : Fraction.Rational) (different : reported ≠ requested)
  /-- A tagged Gaussian reply has the wrong point or operation. -/ | gaussian (failure : Real.Observation.Failure)

constructive_injectivity Failure

/-- Answer each request using its exact original finite or Gaussian source. -/
@[expose] def original (depth : Nat) : Query → Reply depth
  | .inl point => .inl (SourcePoint.observe (Horner.Real.finiteSource depth) ⟨point, point⟩ point le_rfl le_rfl)
  | .inr question => .inr (Real.Observation.original question)

/-- The actual common child supplies its original rational unit tag. -/
@[expose] def tag (depth : Nat) (left : NumericalFrontier (finiteProcess depth))
    (right : NumericalFrontier Horner.Real.source) (index : Independent.Index left right) : Real.Observation.Point :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  ⟨child.start, valid.1, Fraction.Order.Basic.le_trans _ _ _ valid.2.1.le valid.2.2⟩

/-- An exact source observation supplies the original process's state and its same cached reading. -/
@[expose] def exactReply (depth : Nat) (point : Fraction.Rational) (request : AccuracyRequest)
    (previous : (finiteProcess depth point).State) (observed : SourcePoint (Horner.Real.finiteSource depth))
    (same : observed.point = point) :
    (NumericalPoint.Selection.request previous : NumericalPoint.Selection (finiteProcess depth) point request).Reply :=
  ⟨⟨previous, rfl⟩, ⟨Purelib.Data.Rat.Interval.exact observed.reading,
    congrArg Purelib.Data.Rat.Interval.exact
      (observed.reading_eq.trans (congrArg (Horner.Real.finiteSource depth) same))⟩⟩

/-- Observe one actual finite-source selection, reusing a sufficient parent without a request. -/
@[expose] def exactSelection (depth : Nat) (point : Fraction.Rational) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection (finiteProcess depth) point request) :
    Program Query (Reply depth) (Except Failure choice.Reply) :=
  match choice with
  | .reuse _ _ _ => .pure (.ok ())
  | .request previous => .request (.inl point) fun returned => match returned with
    | .inr _ => .pure (.error (.owner (.inl point)))
    | .inl observed =>
        if same : observed.point = point then .pure (.ok (exactReply depth point request previous observed same))
        else .pure (.error (.tag point observed.point same))

/-- The canonical cached reply for an original exact-source selection. -/
@[expose] def exactOriginalReply (depth : Nat) (point : Fraction.Rational) (request : AccuracyRequest) :
    (choice : NumericalPoint.Selection (finiteProcess depth) point request) → choice.Reply
  | .reuse _ _ _ => ()
  | .request previous =>
      ⟨⟨previous, rfl⟩, ⟨Purelib.Data.Rat.Interval.exact (Horner.Real.finiteSource depth point), rfl⟩⟩

/-- Original exact-source execution returns the actual selected point state and reading. -/
theorem exactSelection_original (depth : Nat) (point : Fraction.Rational) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection (finiteProcess depth) point request) :
    ((exactSelection depth point request choice).protocol.run (original depth)).value =
      .ok (exactOriginalReply depth point request choice) := by
  cases choice with
  | reuse retained same accurate => rfl
  | request previous =>
      unfold exactSelection
      change (((if same : point = point then
        (Program.pure (.ok (exactReply depth point request previous
          (SourcePoint.observe (Horner.Real.finiteSource depth) ⟨point, point⟩ point le_rfl le_rfl) same)) :
          Program Query (Reply depth) (Except Failure
            (NumericalPoint.Selection.request previous :
              NumericalPoint.Selection (finiteProcess depth) point request).Reply))
        else .pure (.error (.tag point point same))).protocol).run (original depth)).value = _
      rw [dif_pos rfl]
      rfl

/-- Forward a tagged Gaussian request and reject a finite-source reply. -/
@[expose] def gaussianHandler (depth : Nat) (question : Real.Observation.Query) :
    Program Query (Reply depth) (Except Failure Real.Observation.Reply) :=
  .request (.inr question) fun returned => match returned with
    | .inl _ => .pure (.error (.owner (.inr question)))
    | .inr reply => .pure (.ok reply)

/-- The original mixed source returns the original tagged Gaussian reply. -/
theorem gaussianHandler_original (depth : Nat) (question : Real.Observation.Query) :
    ((gaussianHandler depth question).protocol.run (original depth)).value =
      .ok (Real.Observation.original question) := rfl

variable (depth : Nat) (left : NumericalFrontier (finiteProcess depth))
  (right : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)

/-- The actual left parent decision at one original common occurrence. -/
@[expose] def leftChoice (index : Independent.Index left right) :=
  (Independent.leftParent left right index).selectSaved (tag depth left right index).val request

/-- The actual right parent decision at one original common occurrence. -/
@[expose] def rightChoice (index : Independent.Index left right) :=
  (Independent.rightParent left right index).selectSaved (tag depth left right index).val request

/-- Assemble the original left common-point reply from the returned exact reading. -/
@[expose] def leftReply (index : Independent.Index left right)
    (reply : (leftChoice depth left right request index).Reply) :
    Independent.Reply left right request := by
  let parent := Independent.leftParent left right index
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := leftChoice depth left right request index
  let selected := choice.resolveWith child le_rfl valid.2.1.le reply
  have same : selected.val = Independent.leftPoint left right request index :=
    (congrArg Subtype.val (choice.resolveWith_eq_resolve child le_rfl valid.2.1.le reply)).trans
      (NumericalPoint.selectSaved_resolve_eq_retag parent child child.start le_rfl valid.2.1.le request)
  exact .inl ⟨index, ⟨selected.val, same⟩⟩

/-- Every returned exact selection assembles the same indexed original left point. -/
theorem leftReply_eq (index : Independent.Index left right)
    (reply : (leftChoice depth left right request index).Reply) :
    leftReply depth left right request index reply = Independent.originalReply left right request (.inl index) := by
  let parent := Independent.leftParent left right index
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := leftChoice depth left right request index
  unfold leftReply Independent.originalReply
  apply congrArg Sum.inl
  apply congrArg (fun point : Independent.LeftSelected left right request index =>
    Independent.LeftReply.mk index point)
  apply Subtype.ext
  exact (congrArg Subtype.val (choice.resolveWith_eq_resolve child le_rfl valid.2.1.le reply)).trans
    (NumericalPoint.selectSaved_resolve_eq_retag parent child child.start le_rfl valid.2.1.le request)

/-- Assemble the original right common-point reply from the returned Gaussian state and interval. -/
@[expose] def rightReply (index : Independent.Index left right)
    (reply : (rightChoice depth left right request index).Reply) :
    Independent.Reply left right request := by
  let parent := Independent.rightParent left right index
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := rightChoice depth left right request index
  let selected := choice.resolveWith child le_rfl valid.2.1.le reply
  have same : selected.val = Independent.rightPoint left right request index :=
    (congrArg Subtype.val (choice.resolveWith_eq_resolve child le_rfl valid.2.1.le reply)).trans
      (NumericalPoint.selectSaved_resolve_eq_retag parent child child.start le_rfl valid.2.1.le request)
  exact .inr ⟨index, ⟨selected.val, same⟩⟩

/-- Every returned Gaussian selection assembles the same indexed original right point. -/
theorem rightReply_eq (index : Independent.Index left right)
    (reply : (rightChoice depth left right request index).Reply) :
    rightReply depth left right request index reply = Independent.originalReply left right request (.inr index) := by
  let parent := Independent.rightParent left right index
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := rightChoice depth left right request index
  unfold rightReply Independent.originalReply
  apply congrArg Sum.inr
  apply congrArg (fun point : Independent.RightSelected left right request index =>
    Independent.RightReply.mk index point)
  apply Subtype.ext
  exact (congrArg Subtype.val (choice.resolveWith_eq_resolve child le_rfl valid.2.1.le reply)).trans
    (NumericalPoint.selectSaved_resolve_eq_retag parent child child.start le_rfl valid.2.1.le request)

/-- Lower one original common-point request to its actual finite or Gaussian source operations. -/
@[expose] def handler (question : Independent.Query left right) :
    Program Query (Reply depth) (Except Failure (Independent.Reply left right request)) :=
  match question with
  | .inl index => (exactSelection depth (tag depth left right index).val request
      (leftChoice depth left right request index)).map fun result =>
        result.map (leftReply depth left right request index)
  | .inr index => ((Real.Observation.selection (tag depth left right index) request
      (rightChoice depth left right request index)).substituteChecked (gaussianHandler depth)).map fun result =>
        match result with
        | .error invalid => .error invalid
        | .ok execution => execution.value.mapError Failure.gaussian |>.map (rightReply depth left right request index)

/-- Original mixed replies return the complete original common-point reply at every occurrence. -/
theorem handler_original (question : Independent.Query left right) :
    ((handler depth left right request question).protocol.run (original depth)).value =
      .ok (Independent.originalReply left right request question) := by
  cases question with
  | inl index =>
      unfold handler
      rw [Program.map_execution, Protocol.map_run_value, exactSelection_original]
      apply congrArg Except.ok
      exact leftReply_eq depth left right request index _
  | inr index =>
      unfold handler
      rw [Program.map_execution, Protocol.map_run_value]
      have returned := Program.substituteChecked_value (gaussianHandler depth)
        (Real.Observation.selection (tag depth left right index) request (rightChoice depth left right request index))
        (original depth) Real.Observation.original (gaussianHandler_original depth)
      rw [returned]
      dsimp only
      rw [Real.Observation.selection_original]
      apply congrArg Except.ok
      exact rightReply_eq depth left right request index _

/-- Observe the actual common refinement through its finite-source and Gaussian point operations. -/
@[expose] def computation :=
  (Independent.computation left right request).substituteChecked (handler depth left right request)

/-- Original mixed replies return the complete original indexed common-reading execution. -/
theorem computation_original :
    ((computation depth left right request).protocol.run (original depth)).value =
      .ok ((Independent.computation left right request).protocol.run
        (Independent.originalReply left right request)) := by
  unfold computation
  apply Program.substituteChecked_value
  intro question
  exact handler_original depth left right request question

/-- Replay returns the same complete common-reading execution without source requests. -/
theorem computation_replay :
    (computation depth left right request).protocol.replayExact
      ((computation depth left right request).protocol.run (original depth)).trace =
        .ok (.ok ((Independent.computation left right request).protocol.run
          (Independent.originalReply left right request))) := by
  rw [(computation depth left right request).protocol.replayExact_run, computation_original]

/-- Changes outside the actual finite and Gaussian requests preserve the complete result and trace. -/
theorem payload_erasure {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply depth) :
    let program := computation depth left right request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (original depth)).trace (outside payload)) =
      program.protocol.run (original depth) :=
  (computation depth left right request).protocol.annotation_erasure (original depth) payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points

end
