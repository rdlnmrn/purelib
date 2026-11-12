module

public import Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points
public import Purelib.Integration.Cell.Numerical.Common.Observation.Independent.Cache
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained-bank finite-Taylor and Gaussian common points

The original left and right caller banks are extended with their own frontier
points once. The same effective lists select both the displayed point
requests and the original common-reading assembly. Failed operations retain
their original occurrence, completed readings and actual new point banks.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Cached

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Data.Gaussian
open Purelib.Computation.Query
open Purelib.Integration.Exponential
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Common.Observation

variable (depth : Nat) (left : NumericalFrontier (finiteProcess depth))
  (right : NumericalFrontier Horner.Real.source) (leftBank : List (NumericalPoint (finiteProcess depth)))
  (rightBank : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)

/-- The exact left selection from its supplied effective finite-source bank. -/
@[expose] def leftChoice (index : Independent.Index left right) :=
  NumericalPoint.selectBank (finiteProcess depth) leftBank (tag depth left right index).val request

/-- The exact right selection from its supplied effective Gaussian-source bank. -/
@[expose] def rightChoice (index : Independent.Index left right) :=
  NumericalPoint.selectBank Horner.Real.source rightBank (tag depth left right index).val request

/-- Assemble the exact bank-selected left point from its returned original source reply. -/
@[expose] def leftSelected (index : Independent.Index left right)
    (reply : (leftChoice depth left right leftBank request index).Reply) :
    Independent.Cache.LeftSelected left right leftBank request index := by
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := leftChoice depth left right leftBank request index
  let selected := choice.resolveWith child le_rfl valid.2.1.le reply
  have same : selected.val = (Independent.Cache.leftPoint left right leftBank request index).val :=
    congrArg Subtype.val (NumericalPoint.selectBank_resolveWith_eq_atCached (finiteProcess depth) leftBank
      child child.start le_rfl valid.2.1.le request reply)
  exact ⟨selected.val, same⟩

/-- Assemble the exact bank-selected right point from its returned Gaussian state and interval. -/
@[expose] def rightSelected (index : Independent.Index left right)
    (reply : (rightChoice depth left right rightBank request index).Reply) :
    Independent.Cache.RightSelected left right rightBank request index := by
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let choice := rightChoice depth left right rightBank request index
  let selected := choice.resolveWith child le_rfl valid.2.1.le reply
  have same : selected.val = (Independent.Cache.rightPoint left right rightBank request index).val :=
    congrArg Subtype.val (NumericalPoint.selectBank_resolveWith_eq_atCached Horner.Real.source rightBank
      child child.start le_rfl valid.2.1.le request reply)
  exact ⟨selected.val, same⟩

/-- Returned finite-source data identify the original bank-selected left point. -/
theorem leftSelected_eq (index : Independent.Index left right)
    (reply : (leftChoice depth left right leftBank request index).Reply) :
    leftSelected depth left right leftBank request index reply =
      ⟨(Independent.Cache.leftPoint left right leftBank request index).val, rfl⟩ := by
  apply Subtype.ext
  exact (leftSelected depth left right leftBank request index reply).property

/-- Returned Gaussian data identify the original bank-selected right point. -/
theorem rightSelected_eq (index : Independent.Index left right)
    (reply : (rightChoice depth left right rightBank request index).Reply) :
    rightSelected depth left right rightBank request index reply =
      ⟨(Independent.Cache.rightPoint left right rightBank request index).val, rfl⟩ := by
  apply Subtype.ext
  exact (rightSelected depth left right rightBank request index reply).property

/-- Forward one original mixed query, reporting an absent outer-operation reply at that query. -/
@[expose] def optionalHandler (depth : Nat) (question : Query) :
    Program Query (Option (Reply depth)) (Except Failure (Reply depth)) :=
  .request question fun returned => match returned with
    | none => .pure (.error (.owner question))
    | some reply => .pure (.ok reply)

/-- Forward one tagged Gaussian operation, checking both outer and original source owners. -/
@[expose] def optionalGaussianHandler (depth : Nat) (question : Real.Observation.Query) :
    Program Query (Option (Reply depth)) (Except Failure Real.Observation.Reply) :=
  .request (.inr question) fun returned => match returned with
    | none => .pure (.error (.owner (.inr question)))
    | some (.inl _) => .pure (.error (.owner (.inr question)))
    | some (.inr reply) => .pure (.ok reply)

/-- The original indexed common occurrence retained by a pending request. -/
@[expose] def PendingIndex := Independent.Index left right

/-- The exact left observation already returned at this common occurrence. -/
@[expose] def PendingLeft (index : PendingIndex depth left right) :=
  Independent.Cache.LeftSelected left right leftBank request index

/-- The original Gaussian source predecessor at one common occurrence. -/
@[expose] def PendingPrevious (index : PendingIndex depth left right) :=
  (Horner.Real.source (tag depth left right index).val).State

/-- The retained bank chose this exact original Gaussian predecessor. -/
@[expose] def PendingSelected (index : PendingIndex depth left right)
    (previous : PendingPrevious depth left right index) : Prop :=
  rightChoice depth left right rightBank request index = .request previous

/-- The original refinement response returned for a selected predecessor. -/
@[expose] def PendingReturned (index : PendingIndex depth left right)
    (previous : PendingPrevious depth left right index) :=
  Coordinate.Observation.ReturnedState
    (Horner.Real.originalState (tag depth left right index).val (tag depth left right index).property previous)
    request.tolerance request.positive

section
attribute [local irreducible] PendingIndex PendingLeft PendingPrevious PendingSelected PendingReturned

set_option genInjectivity false in
/-- The actual failed Gaussian point request after its refinement was returned. -/
structure Pending (index : PendingIndex depth left right) where
  /-- The exact certified left point already returned at this occurrence. -/
  leftPoint : PendingLeft depth left right leftBank request index
  /-- The exact original source predecessor selected by the retained right bank. -/
  previous : PendingPrevious depth left right index
  /-- The stored predecessor is exactly the actual selected request branch. -/
  selected : PendingSelected depth left right rightBank request index previous
  /-- The exact original Gaussian state already returned by that branch. -/
  next : PendingReturned depth left right request index previous
  /-- The original point, operation or outer-owner failure. -/
  reason : Points.Failure

constructive_injectivity Pending

set_option genInjectivity false in
/-- An invalid common request with optional exact pending Gaussian work. -/
inductive ProgressFailure where
  /-- A source operation failed before a reusable Gaussian refinement was returned. -/
  | source (reason : Points.Failure)
  /-- The specified original occurrence retains the successful Gaussian refinement. -/
  | pending (index : PendingIndex depth left right)
      (receipt : Pending depth left right leftBank rightBank request index)

constructive_injectivity ProgressFailure
end

/-- The enclosing cache failure identifies the same occurrence as a pending receipt. -/
def ProgressFailure.Matches (failed : Independent.Index left right) :
    ProgressFailure depth left right leftBank rightBank request → Prop
  | .source _ => True
  | .pending index _ => index = failed

/-- Original optional replies retain the original mixed source response. -/
theorem optionalHandler_original (depth : Nat) (question : Query) :
    ((optionalHandler depth question).protocol.run (fun query => some (original depth query))).value =
      .ok (original depth question) := rfl

/-- Original optional replies retain the original tagged Gaussian response. -/
theorem optionalGaussianHandler_original (depth : Nat) (question : Real.Observation.Query) :
    ((optionalGaussianHandler depth question).protocol.run (fun query => some (original depth query))).value =
      .ok (Real.Observation.original question) := rfl

/-- Check one tagged Gaussian reply against its exact rational source owner. -/
@[expose] def checkedPoint (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request Nat) :
    Program Query (Option (Reply depth))
      (Except Points.Failure (Coordinate.Observation.Reply (Real.Observation.process point))) :=
  Real.Observation.pointWith point (optionalGaussianHandler depth) Points.Failure.gaussian operation

/-- Check one actual tagged Gaussian operation, retaining every boundary failure as data. -/
@[expose] def checkedGaussian (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request Nat) :
    Program Query (Option (Reply depth))
      (Except Points.Failure (Coordinate.Observation.Response (Real.Observation.process point) operation)) :=
  Real.Observation.checkedWith point (optionalGaussianHandler depth) Points.Failure.gaussian operation

/-- Original mixed replies return the original point-owned Gaussian reply. -/
theorem checkedPoint_original (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request Nat) :
    ((checkedPoint depth point operation).protocol.run (fun question => some (original depth question))).value =
      .ok (Coordinate.Observation.original (Real.Observation.process point) operation) := by
  unfold checkedPoint Real.Observation.pointWith
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value (optionalGaussianHandler depth)
    (Real.Observation.pointHandler point operation) (fun question => some (original depth question))
    Real.Observation.original (optionalGaussianHandler_original depth)]
  dsimp only
  rw [Real.Observation.pointHandler_original]
  rfl

/-- Original tagged replies return the exact original checked Gaussian response. -/
theorem checkedGaussian_original (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request Nat) :
    ((checkedGaussian depth point operation).protocol.run (fun question => some (original depth question))).value =
      .ok (Coordinate.Observation.original_request (Real.Observation.process point) operation ▸
        (Coordinate.Observation.original (Real.Observation.process point) operation).2) :=
  Real.Observation.checkedWith_original point (optionalGaussianHandler depth) Points.Failure.gaussian
    operation (fun question => some (original depth question)) (optionalGaussianHandler_original depth)

set_option genInjectivity false in
/-- A cached failure does not identify the requested pending occurrence. -/
inductive PendingAccessFailure where
  /-- No Gaussian refinement had been retained at this failure. -/
  | unavailable (reason : Points.Failure)
  /-- The retained receipt names a different original common occurrence. -/
  | occurrence (reported failed : PendingIndex depth left right) (different : reported ≠ failed)
constructive_injectivity PendingAccessFailure

/-- A pending receipt certified as the exact cause and occurrence of a cached failure. -/
abbrev PendingView (savedLeft : List (NumericalPoint (finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (failure : Independent.Cache.Failure left right request
      (ProgressFailure depth left right leftBank rightBank request) savedLeft savedRight) :=
  {pair : Σ index : PendingIndex depth left right,
      Pending depth left right leftBank rightBank request index //
    pair.1 = failure.failed ∧ failure.reason = .pending pair.1 pair.2}

/-- Check that the actual retained pending reason belongs to the failed occurrence. -/
@[expose] def pendingView (savedLeft : List (NumericalPoint (finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (failure : Independent.Cache.Failure left right request
      (ProgressFailure depth left right leftBank rightBank request) savedLeft savedRight) :
    Except (PendingAccessFailure depth left right)
      (PendingView depth left right leftBank rightBank request savedLeft savedRight failure) := by
  letI : DecidableEq (PendingIndex depth left right) :=
    inferInstanceAs (DecidableEq (Fin (Independent.occurrences left right).length))
  exact match found : failure.reason with
  | .source reason => .error (.unavailable reason)
  | .pending index receipt =>
      if same : index = failure.failed then .ok ⟨⟨index, receipt⟩, same, found⟩
      else .error (.occurrence index failure.failed same)

/-- A sufficient retained finite-source point causes no exact-source operation. -/
theorem left_sufficient (index : Independent.Index left right)
    (retained : {point : NumericalPoint (finiteProcess depth) //
      point.point = (tag depth left right index).val ∧ point.reading.width < request.tolerance})
    (found : NumericalPoint.findSufficient leftBank (tag depth left right index).val request = some retained)
    (oracle : Query → Option (Reply depth)) :
    (((exactSelection depth (tag depth left right index).val request
      (leftChoice depth left right leftBank request index)).substituteChecked
        (optionalHandler depth)).protocol.run oracle).trace = [] := by
  unfold leftChoice
  rw [NumericalPoint.selectBank_sufficient _ _ _ retained found]
  rfl

/-- A sufficient retained numerical point causes no tagged Gaussian operation. -/
theorem right_sufficient (index : Independent.Index left right)
    (retained : {point : NumericalPoint Horner.Real.source //
      point.point = (tag depth left right index).val ∧ point.reading.width < request.tolerance})
    (found : NumericalPoint.findSufficient rightBank (tag depth left right index).val request = some retained)
    (oracle : Query → Option (Reply depth)) :
    (((Real.Observation.selection (tag depth left right index) request
      (rightChoice depth left right rightBank request index)).substituteChecked
        (optionalGaussianHandler depth)).protocol.run oracle).trace = [] := by
  unfold rightChoice
  rw [NumericalPoint.selectBank_sufficient _ _ _ retained found]
  rfl

/-- Select an already chosen Gaussian branch while retaining any returned partial refinement. -/
@[expose] def progressSelectionWith (index : Independent.Index left right)
    (first : Independent.Cache.LeftSelected left right leftBank request index)
    (choice : NumericalPoint.Selection Horner.Real.source (tag depth left right index).val request)
    (selected : rightChoice depth left right rightBank request index = choice) :
    Program Query (Option (Reply depth))
      (Except (ProgressFailure depth left right leftBank rightBank request) choice.Reply) := by
  cases choice with
  | reuse retained same accurate => exact .pure (.ok ())
  | request previous =>
      let point := tag depth left right index
      let state := Horner.Real.originalState point.val point.property previous
      have chosen : PendingSelected depth left right rightBank request index previous := selected
      exact (Coordinate.Observation.coordinateWith (checkedGaussian depth point)
        Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive).map fun result =>
        match result with
        | .error (.refinement invalid) => .error (.source invalid)
        | .error (.ball next invalid) => .error (.pending index ⟨first, previous, chosen, next, invalid⟩)
        | .ok next => .ok (Real.Observation.requestReply point previous request next)

/-- Select the actual right Gaussian bank branch, retaining partial refinement work. -/
@[expose] def progressSelection (index : Independent.Index left right)
    (first : Independent.Cache.LeftSelected left right leftBank request index) :=
  progressSelectionWith depth left right leftBank rightBank request index first
    (rightChoice depth left right rightBank request index) rfl

section
attribute [local irreducible] checkedGaussian Real.Observation.requestReply

/-- Original replies return the supplied actual right Gaussian branch. -/
theorem progressSelectionWith_original (index : Independent.Index left right)
    (first : Independent.Cache.LeftSelected left right leftBank request index)
    (choice : NumericalPoint.Selection Horner.Real.source (tag depth left right index).val request)
    (selected : rightChoice depth left right rightBank request index = choice) :
    ((progressSelectionWith depth left right leftBank rightBank request index first choice selected).protocol.run
      (fun question => some (original depth question))).value =
        .ok (Real.Observation.originalSelectionReply (tag depth left right index) request choice) := by
  cases choice with
  | reuse retained same accurate => rfl
  | request previous =>
      unfold progressSelectionWith
      rw [Program.map_execution, Protocol.map_run_value]
      let point := tag depth left right index
      let state : Coordinate.State (Real.Observation.process point) (0 : Nat) Basic.Canonical.re :=
        Horner.Real.originalState point.val point.property previous
      let ask : (operation : Coordinate.Observation.Request (Real.Observation.process point).State) →
          Program Query (Option (Reply depth))
            (Except Points.Failure (Coordinate.Observation.Response (Real.Observation.process point) operation)) :=
        fun operation => checkedGaussian depth point operation
      have answer (operation : Coordinate.Observation.Request (Real.Observation.process point).State) :
          ((ask operation).protocol.run (fun question => some (original depth question))).value =
            .ok (Coordinate.Observation.original_request (Real.Observation.process point) operation ▸
              (Coordinate.Observation.original (Real.Observation.process point) operation).2) :=
        checkedGaussian_original depth point operation
      have actual := Coordinate.Observation.coordinateWith_original ask
        Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive
        (fun question => some (original depth question)) answer
      let finish := fun result : Except
          (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Points.Failure)
          (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
            state request.tolerance request.positive) =>
        match result with
        | .error (.refinement invalid) => Except.error (ProgressFailure.source invalid)
        | .error (.ball next invalid) =>
            Except.error (ProgressFailure.pending index ⟨first, previous, selected, next, invalid⟩)
        | .ok next => Except.ok (Real.Observation.requestReply point previous request next)
      change finish (((Coordinate.Observation.coordinateWith ask Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive).protocol.run
          (fun question => some (original depth question))).value) = _
      have same := congrArg finish actual
      refine same.trans ?_
      apply congrArg Except.ok
      exact Real.Observation.selectionReply_unique _ _ _ _ _

/-- Original replies return the actual selected right Gaussian branch. -/
theorem progressSelection_original (index : Independent.Index left right)
    (first : Independent.Cache.LeftSelected left right leftBank request index) :
    ((progressSelection depth left right leftBank rightBank request index first).protocol.run
      (fun question => some (original depth question))).value =
        .ok (Real.Observation.originalSelectionReply (tag depth left right index) request
          (rightChoice depth left right rightBank request index)) :=
  progressSelectionWith_original depth left right leftBank rightBank request index first
    (rightChoice depth left right rightBank request index) rfl

end

/-- The optional tagged handler records its one original question and reply. -/
theorem optionalGaussianHandler_trace (depth : Nat) (question : Real.Observation.Query)
    (oracle : Query → Option (Reply depth)) :
    ((optionalGaussianHandler depth question).protocol.run oracle).trace =
      [⟨.inr question, oracle (.inr question)⟩] := by
  unfold optionalGaussianHandler
  change ⟨.inr question, oracle (.inr question)⟩ ::
    ((match oracle (.inr question) with
      | none => Program.pure (.error (Points.Failure.owner (.inr question)))
      | some (.inl _) => Program.pure (.error (Points.Failure.owner (.inr question)))
      | some (.inr reply) => Program.pure (.ok reply) :
        Program Query (Option (Reply depth))
          (Except Points.Failure Real.Observation.Reply)).protocol.run oracle).trace = _
  cases oracle (.inr question) with
  | none => rfl
  | some reply => cases reply <;> rfl

/-- A tagged point check records exactly the original requested operation. -/
theorem checkedPoint_trace (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request Nat) (oracle : Query → Option (Reply depth)) :
    ((checkedPoint depth point operation).protocol.run oracle).trace =
      [⟨.inr (point, operation), oracle (.inr (point, operation))⟩] :=
  (Real.Observation.pointWith_trace point (optionalGaussianHandler depth) Points.Failure.gaussian
    operation oracle).trans
    (optionalGaussianHandler_trace depth (point, operation) oracle)

/-- A checked tagged Gaussian operation records exactly its one requested reply. -/
theorem checkedGaussian_trace (depth : Nat) (point : Real.Observation.Point)
    (operation : Coordinate.Observation.Request (Real.Observation.process point).State)
    (oracle : Query → Option (Reply depth)) :
    ((checkedGaussian depth point operation).protocol.run oracle).trace =
      [⟨.inr (point, operation), oracle (.inr (point, operation))⟩] :=
  (Real.Observation.checkedWith_trace point (optionalGaussianHandler depth) Points.Failure.gaussian
    operation oracle).trans
    (optionalGaussianHandler_trace depth (point, operation) oracle)

/-- Resume the interrupted point with its exact returned refinement. -/
@[expose] def resumePoint (index : Independent.Index left right)
    (receipt : Pending depth left right leftBank rightBank request index) :
    Program Query (Option (Reply depth))
      (Except (Pending depth left right leftBank rightBank request index)
        (Independent.Cache.RightSelected left right rightBank request index)) := by
  let point := tag depth left right index
  let previous := Horner.Real.originalState point.val point.property receipt.previous
  let ask := checkedGaussian depth point
  exact (Coordinate.Observation.resumeWith ask Norm.Coordinates.re_sub_sq_le_basic_normSq previous
      request.tolerance request.positive receipt.next).map fun result =>
    match result with
    | .error (.refinement reason) => .error { receipt with reason := reason }
    | .error (.ball _ reason) => .error { receipt with reason := reason }
    | .ok next =>
      let reply := Real.Observation.requestReply point receipt.previous request next
      let selectedReply : (rightChoice depth left right rightBank request index).Reply :=
        receipt.selected.symm ▸ reply
      .ok (rightSelected depth left right rightBank request index selectedReply)

/-- Resume the interrupted common pair from its exact retained left point and right refinement. -/
@[expose] def resumePair (index : Independent.Index left right)
    (receipt : Pending depth left right leftBank rightBank request index) :
    Program Query (Option (Reply depth))
      (Except (Pending depth left right leftBank rightBank request index)
        (Independent.Cache.SelectedPair left right leftBank rightBank request index)) :=
  (resumePoint depth left right leftBank rightBank request index receipt).map fun result =>
    result.map fun rightPoint => (receipt.leftPoint, rightPoint)

section
attribute [local irreducible] checkedGaussian Real.Observation.requestReply

/-- Original replies complete the retained pair using the same returned refinement. -/
theorem resumePair_original (index : Independent.Index left right)
    (receipt : Pending depth left right leftBank rightBank request index) :
    ((resumePair depth left right leftBank rightBank request index receipt).protocol.run
      (fun question => some (original depth question))).value =
        .ok (receipt.leftPoint, ⟨(Independent.Cache.rightPoint left right rightBank request index).val, rfl⟩) := by
  unfold resumePair resumePoint
  rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value]
  let point := tag depth left right index
  let state : Coordinate.State (Real.Observation.process point) (0 : Nat) Basic.Canonical.re :=
    Horner.Real.originalState point.val point.property receipt.previous
  let ask : (operation : Coordinate.Observation.Request (Real.Observation.process point).State) →
      Program Query (Option (Reply depth))
        (Except Points.Failure (Coordinate.Observation.Response (Real.Observation.process point) operation)) :=
    fun operation => checkedGaussian depth point operation
  have answer (operation : Coordinate.Observation.Request (Real.Observation.process point).State) :
      ((ask operation).protocol.run (fun question => some (original depth question))).value =
        .ok (Coordinate.Observation.original_request (Real.Observation.process point) operation ▸
          (Coordinate.Observation.original (Real.Observation.process point) operation).2) :=
    checkedGaussian_original depth point operation
  have actual := Coordinate.Observation.resumeWith_original ask
    Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive receipt.next
    (fun question => some (original depth question)) answer
  let finish := fun result : Except
      (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Points.Failure)
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive) =>
    (match result with
    | .error (.refinement invalid) => Except.error { receipt with reason := invalid }
    | .error (.ball _ invalid) => Except.error { receipt with reason := invalid }
    | .ok next =>
        let reply := Real.Observation.requestReply point receipt.previous request next
        let selectedReply : (rightChoice depth left right rightBank request index).Reply :=
          receipt.selected.symm ▸ reply
        Except.ok (rightSelected depth left right rightBank request index selectedReply)).map
          (fun rightPoint => (receipt.leftPoint, rightPoint))
  change finish (((Coordinate.Observation.resumeWith ask Norm.Coordinates.re_sub_sq_le_basic_normSq
    state request.tolerance request.positive receipt.next).protocol.run
      (fun question => some (original depth question))).value) = _
  have same := congrArg finish actual
  refine same.trans ?_
  apply congrArg Except.ok
  apply Prod.ext
  · rfl
  · exact rightSelected_eq depth left right rightBank request index _

end

/-- Resuming one retained pair issues exactly its saved Gaussian state's ball request. -/
theorem resumePair_trace (index : Independent.Index left right)
    (receipt : Pending depth left right leftBank rightBank request index) (oracle : Query → Option (Reply depth)) :
    ((resumePair depth left right leftBank rightBank request index receipt).protocol.run oracle).trace =
      [⟨.inr (tag depth left right index, .ball receipt.next.val),
        oracle (.inr (tag depth left right index, .ball receipt.next.val))⟩] := by
  unfold resumePair resumePoint Coordinate.Observation.resumeWith
  rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
    Program.map_execution, Protocol.map_run_trace]
  exact checkedGaussian_trace depth (tag depth left right index) (.ball receipt.next.val) oracle

/-- Select both actual owner-specific common points while retaining partial work on failure. -/
@[expose] def pair (savedLeft : List (NumericalPoint (finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source)) (index : Independent.Index left right) :
    Program Query (Option (Reply depth))
      (Except (Independent.Cache.Failure left right request
        (ProgressFailure depth left right leftBank rightBank request) savedLeft savedRight)
        (Independent.Cache.SelectedPair left right leftBank rightBank request index)) :=
  ((exactSelection depth (tag depth left right index).val request
      (leftChoice depth left right leftBank request index)).substituteChecked (optionalHandler depth)).bind fun first =>
    match first with
    | .error invalid => .pure (.error
        (Independent.Cache.Failure.initial left right request savedLeft savedRight index (.source invalid)))
    | .ok execution => match execution.value with
      | .error invalid => .pure (.error
        (Independent.Cache.Failure.initial left right request savedLeft savedRight index (.source invalid)))
      | .ok first =>
          let selected := leftSelected depth left right leftBank request index first
          (progressSelection depth left right leftBank rightBank request index selected).map fun second =>
            match second with
            | .error invalid => .error (Independent.Cache.Failure.afterLeft left right request savedLeft savedRight
                index invalid selected.val)
            | .ok reply => .ok (selected, rightSelected depth left right rightBank request index reply)

/-- Original finite and Gaussian replies return the actual two bank-selected point owners. -/
theorem pair_original (savedLeft : List (NumericalPoint (finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source)) (index : Independent.Index left right) :
    ((pair depth left right leftBank rightBank request savedLeft savedRight index).protocol.run
      (fun question => some (original depth question))).value =
        .ok (⟨(Independent.Cache.leftPoint left right leftBank request index).val, rfl⟩,
          ⟨(Independent.Cache.rightPoint left right rightBank request index).val, rfl⟩) := by
  unfold pair
  rw [Program.bind_execution, Protocol.bind_run_value]
  have first := Program.substituteChecked_value (optionalHandler depth)
    (exactSelection depth (tag depth left right index).val request (leftChoice depth left right leftBank request index))
    (fun question => some (original depth question)) (original depth) (optionalHandler_original depth)
  rw [first]
  dsimp only
  rw [exactSelection_original]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_value]
  rw [progressSelection_original]
  apply congrArg Except.ok
  apply Prod.ext
  · exact leftSelected_eq depth left right leftBank request index _
  · exact rightSelected_eq depth left right rightBank request index _

/-- Observe the common refinement and retain its exact certified prefix on failure.

Both effective banks are built once and passed unchanged to every point
selection. A failing right ball read additionally retains the actual left
point and already returned right Gaussian refinement. -/
@[expose] def computationProgress :=
  let actualLeft := Independent.Cache.leftAvailable left leftBank
  let actualRight := Independent.Cache.rightAvailable right rightBank
  Independent.Cache.computationWithPairProgress left right actualLeft actualRight request leftBank rightBank
    (pair depth left right actualLeft actualRight request leftBank rightBank)

/-- Observe the original common refinement, projecting only the batch wrapper on failure. -/
@[expose] def computation :=
  (computationProgress depth left right leftBank rightBank request).map fun returned =>
    returned.mapError (fun stopped => stopped.reason)

/-- Original replies return the actual original two-bank common reading collection. -/
theorem computationProgress_original :
    let actualLeft := Independent.Cache.leftAvailable left leftBank
    let actualRight := Independent.Cache.rightAvailable right rightBank
    ((computationProgress depth left right leftBank rightBank request).protocol.run
      (fun question => some (original depth question))).value =
        .ok (NumericalFrontier.Common.Cache.commonReadings left right actualLeft actualRight request) := by
  let actualLeft := Independent.Cache.leftAvailable left leftBank
  let actualRight := Independent.Cache.rightAvailable right rightBank
  change ((computationProgress depth left right leftBank rightBank request).protocol.run
    (fun question => some (original depth question))).value = _
  unfold computationProgress Independent.Cache.computationWithPairProgress Independent.Cache.batchWithProgress
  rw [Program.map_execution, Protocol.map_run_value,
    Program.certifiedBatchProgress_original (Independent.Cache.originalChild left right actualLeft actualRight request)
      (Independent.Cache.SelectedPair left right actualLeft actualRight request)
      (Independent.Cache.returnedChild left right actualLeft actualRight request)
      (Independent.Cache.returnedChild_eq left right actualLeft actualRight request)
      (fun index points failure => Independent.Cache.Failure.prepend left right actualLeft actualRight request
        leftBank rightBank index points failure)
      (pair depth left right actualLeft actualRight request leftBank rightBank)
      (fun question => some (original depth question))
      (fun index => (⟨(Independent.Cache.leftPoint left right actualLeft request index).val, rfl⟩,
        ⟨(Independent.Cache.rightPoint left right actualRight request index).val, rfl⟩))
      (pair_original depth left right actualLeft actualRight request leftBank rightBank)]
  apply congrArg Except.ok
  exact Independent.Cache.assemble_eq left right actualLeft actualRight request _

/-- The projected original computation returns the same actual two-bank readings. -/
theorem computation_original :
    let actualLeft := Independent.Cache.leftAvailable left leftBank
    let actualRight := Independent.Cache.rightAvailable right rightBank
    ((computation depth left right leftBank rightBank request).protocol.run
      (fun question => some (original depth question))).value =
        .ok (NumericalFrontier.Common.Cache.commonReadings left right actualLeft actualRight request) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, computationProgress_original]
  rfl

/-- Exact replay preserves a retained certified prefix and the actual first failure. -/
theorem progress_replay (oracle : Query → Option (Reply depth)) :
    let program := computationProgress depth left right leftBank rightBank request
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value :=
  (computationProgress depth left right leftBank rightBank request).protocol.replayExact_run oracle

/-- Exact replay preserves the actual returned common readings or first failure and its saved work. -/
theorem replay (oracle : Query → Option (Reply depth)) :
    let program := computation depth left right leftBank rightBank request
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value :=
  (computation depth left right leftBank rightBank request).protocol.replayExact_run oracle

/-- Replies outside the executed mixed common trace preserve the complete result and trace. -/
theorem payload_erasure (oracle : Query → Option (Reply depth)) {Payload : Type} (payload : Payload)
    (outside : Payload → Query → Option (Reply depth)) :
    let program := computation depth left right leftBank rightBank request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation depth left right leftBank rightBank request).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Cached

end
