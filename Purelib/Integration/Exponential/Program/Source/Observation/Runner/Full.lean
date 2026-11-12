module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Saved
public import Purelib.Integration.Exponential.Equivalence.Existing
public import Purelib.Integration.Cell.Source.Comparison.Observation.Cache
public import Purelib.Computation.Query.Program.Certified.Cache

/-!
# Original exponential runner and source comparison in one observation

The original integration model-query program runs through proof-bearing model
receipts. Its actual returned model log constructs the existing successful
runner record without re-executing the runner. The selected cached model in
that record is then used by the two-stage source comparison, whose source
requests follow the runner's model requests in the same displayed trace.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Full

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.CCL.Progressive
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.CCL
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.Integration.SourceFrontier
open Purelib.Integration.SourceFrontier.Comparison.Observation
open Purelib.Integration.SourceFrontier.Continuous
open Purelib.Integration.SourceFrontier.Continuous.Observation

set_option genInjectivity false in
/-- An original retained exponential runner request and one independent comparison-stage request. -/
structure Input (policy rightPolicy : Geometry.Policy) (schedule rightSchedule : PositiveStride)
    (extraDepth rightExtra : Nat) where
  /-- The exact original runner's shared selection and model caches. -/ retained :
    Program.Retained policy schedule extraDepth
  /-- Actual model receipts retained from earlier requests on this same original program. -/
  bank : List (Model.Receipt retained)
  /-- The original positive integration observation request. -/ request : CertifiedProgram.Request
  /-- The requested finite output prefix length. -/ count : Nat
  /-- The positive source-enclosure request for the selected runner stage. -/ accuracy : AccuracyRequest
  /-- The independent original comparison-stage request and its own caches. -/ right :
    StageComparison.Request rightPolicy rightSchedule rightExtra
  /-- Earlier source comparisons on the same original program and right stage. -/ saved :
    List (Runner.Saved retained right)

namespace Input

/-- The original runner's selected stage index before its model query is answered. -/
@[expose] def selectedIndex {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :
    Nat :=
  IntegrationReplay.selectedIndex (control input.retained.program) input.request

/-- Model receipt selection starts with the supplied bank and then reuses missing saved-stage receipts. -/
@[expose] def receiptBank {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :=
  Runner.Saved.mergeReceipts input.bank input.saved

/-- The supplied bank retains its exact precedence in the effective receipt bank. -/
theorem receiptBank_prefix {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :
    ∃ added, input.receiptBank = input.bank ++ added :=
  Runner.Saved.mergeReceipts_prefix input.saved input.bank

/-- Each supplied saved source comparison contributes its original model receipt to the effective bank. -/
theorem receiptBank_contains_saved {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)
    (saved : Runner.Saved input.retained input.right) (member : saved ∈ input.saved) :
    saved.receipt ∈ input.receiptBank :=
  Runner.Saved.mergeReceipts_contains input.saved input.bank saved member

/-- Every supplied saved comparison produces an actual model-cache hit at its original stage. -/
theorem receiptBank_finds_saved {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)
    (saved : Runner.Saved input.retained input.right) (member : saved ∈ input.saved) :
    ∃ found, Program.Certified.Cache.find (Model.receiptSource input.retained) saved.receipt.index input.receiptBank =
      some found :=
  Program.Certified.Cache.find_of_member (Model.receiptSource input.retained) saved.receipt.index input.receiptBank
    saved.receipt (input.receiptBank_contains_saved saved member) rfl

/-- The original model-query construction for the same retained program, request and bit count. -/
@[expose] def modelProgram {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra) :=
  Expansion.program (control input.retained.program) input.request input.count

end Input

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

/-- The actual selected receipt, certified against the original selected query. -/
abbrev Selected := {receipt : Model.Receipt input.retained //
  receipt = Model.originalReply input.retained input.selectedIndex}

/-- The source request consumes the exact selection and model carried by the receipt. -/
@[expose] def selectedRequest (selected : Selected input) :=
  StageComparison.Request.withSelected input.retained selected.val.index selected.val.selection
    selected.val.selection_eq selected.val.model selected.val.model_eq input.accuracy

/-- The source request keeps the selection returned by the original model query. -/
theorem selectedRequest_selection (selected : Selected input) :
    (selectedRequest input selected).selection = selected.val.selection := rfl

/-- The source request keeps the model returned by the same original query. -/
theorem selectedRequest_stage (selected : Selected input) :
    (selectedRequest input selected).stage = selected.val.model := rfl

/-- The returned model is the snapshot of the same returned selection and geometry. -/
theorem selected_model_eq_snapshot (selected : Selected input) :
    selected.val.model = selected.val.selection.snapshot extraDepth :=
  selected.val.model_eq.trans ((input.retained.stage_eq selected.val.index).trans
    (congrArg (fun selection => selection.snapshot extraDepth) selected.val.selection_eq).symm)

/-- Every certified selected receipt is the same original indexed receipt. -/
instance : DecidableEq (Selected input) := by
  intro first second
  exact isTrue (Subtype.ext (first.property.trans second.property.symm))

set_option genInjectivity false in
/-- One original fresh-stage, saved-frontier or common-comparison source request. -/
inductive SourceOperation (selected : Selected input) where
  /-- A fresh original stage or its common comparison. -/ | fresh
      (question : StageComparison.Question (selectedRequest input selected) input.right)
  /-- A saved left-frontier continuation request. -/ | refine
      (question : Continuation.Query (selectedPreparation selected.val.selection input.accuracy))
  /-- A common-point request for the two retained source owners. -/ | common
      (question : Comparison.Observation.Query)
  deriving @[expose] DecidableEq

/-- Source questions carry the actual selected receipt that owns their source. -/
abbrev SourceQuestion := Σ selected : Selected input, SourceOperation input selected

/-- Source questions compare their original operation after identifying the certified receipt. -/
instance : DecidableEq (SourceQuestion input) := by
  intro first second
  cases first with
  | mk firstSelected firstQuestion =>
    cases second with
    | mk secondSelected secondQuestion =>
      have same : firstSelected = secondSelected :=
        Subtype.ext (firstSelected.property.trans secondSelected.property.symm)
      cases same
      by_cases equal : firstQuestion = secondQuestion
      · cases equal
        exact isTrue rfl
      · exact isFalse (fun equal' => equal (by cases equal'; rfl))

/-- The original model request or one source question carrying its actual selected receipt. -/
abbrev Question := Sum Nat (SourceQuestion input)

/-- Executable equality distinguishes model and source requests and compares their original occurrences. -/
instance : DecidableEq (Question input) := by
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
      by_cases same : first = second
      · cases same
        exact isTrue rfl
      · exact isFalse (fun equal => same (by cases equal; rfl))

set_option genInjectivity false in
/-- A fresh-stage, saved-frontier or common-comparison reply with its original owner. -/
inductive SourceResponse (selected : Selected input) where
  /-- The original two-stage source reply. -/ | fresh
      (reply : StageComparison.Reply (selectedRequest input selected) input.right)
  /-- A saved left-frontier source reply. -/ | refine
      (point : SourcePoint (selectedRequest input selected).source)
  /-- A common-point reply from its original left or right source. -/ | common
      (reply : Comparison.Observation.Reply (selectedRequest input selected).source input.right.source)

/-- A source reply retains the actual selected receipt and its dependent source owner. -/
abbrev SourceReply := Σ selected : Selected input, SourceResponse input selected

/-- A model receipt or source reply retains its actual original operation and owner. -/
abbrev Reply := Sum (Model.Receipt input.retained) (SourceReply input)

/-- The original model execution with its exact retained-program certificate. -/
abbrev ModelExecution := Model.Certified input.retained input.modelProgram

/-- The original model receipt execution and its complete certified model projection. -/
abbrev ReceiptExecution := Program.Certified.Execution (Model.receiptSource input.retained) input.modelProgram

/-- A receipt execution with its actual updated bank and retained original bank. -/
abbrev CachedExecution := Program.Certified.Cache.Completed
  (Model.receiptSource input.retained) input.receiptBank input.modelProgram

/-- The original successful runner record indexed by its exact retained program. -/
abbrev Recorded := Record.Recorded input.retained.program input.request input.count

set_option genInjectivity false in
/-- The first invalid operation or actual original runner failure in the combined construction. -/
inductive Failure where
  /-- A model miss received a wrong operation or a receipt for another original index. -/ | model
      (invalid : Program.Certified.Cache.Failure (Model.receiptSource input.retained))
  /-- The runner failed after the actual completed receipt execution and its updated bank. -/ | runner
      (execution : CachedExecution input) (failure : Data.CCL.Transducer.Replay.Failure)
      (value_eq : execution.execution.val.value = .error failure)
  /-- A source request received a model receipt after the runner succeeded. -/ | sourceOperation
      (execution : CachedExecution input) (recorded : Recorded input) (requested : SourceQuestion input)
  /-- The fresh original stage comparison failed at its actual selected receipt. -/ | source
      (execution : CachedExecution input) (recorded : Recorded input) (selected : Selected input)
      (invalid : StageComparison.Failure (selectedRequest input selected) input.right)
  /-- Comparing a new left stage with the saved right frontier rejected a source reply. -/ | changedCommon
      (execution : CachedExecution input) (recorded : Recorded input) (saved : Runner.Saved input.retained input.right)
      (selected : Selected input) (stage : Source.Result policy schedule extraDepth selected.val.index input.accuracy)
      (invalid : Comparison.Observation.Failure)
  /-- A continued left frontier rejected an actual source reply. -/ | refine
      (execution : CachedExecution input) (recorded : Recorded input) (saved : Runner.Saved input.retained input.right)
      (invalid : Continuation.Failure (selectedPreparation saved.receipt.selection input.accuracy))
  /-- Common comparison rejected an actual source reply after the retained left continuation. -/ | common
      (execution : CachedExecution input) (recorded : Recorded input) (saved : Runner.Saved input.retained input.right)
      (step : Producer.Continuation (producer (Horner.Real.finiteModulus saved.receipt.selection.depth)) saved.left)
      (invalid : Comparison.Observation.Failure)

set_option genInjectivity false in
/-- The actual runner record and selected receipt from one completed model acquisition. -/
structure Chosen where
  /-- The complete logical receipt execution and actual updated bank. -/ completed : CachedExecution input
  /-- The exact runner observation and returned ordered model-query log. -/ recorded : Recorded input
  /-- The receipt execution returned this same original observation. -/ receipt_value :
    completed.execution.val.value = .ok recorded.observation
  /-- The actual selected receipt retained from the model execution. -/ selected : Selected input
  /-- The selected receipt is the actual first returned receipt in the completed execution. -/ selected_receipt :
    selected.val = Model.selectedReceipt input.retained input.request input.count completed.execution
      recorded.observation receipt_value
  /-- Its model is the same first model returned in the original runner record. -/ selected_model :
    selected.val.model = recorded.selectedExchange.reply

/-- A certified continuation of the exact saved left frontier for this request. -/
abbrev SavedStep (saved : Runner.Saved input.retained input.right) :=
  Continuation.CertifiedStep (Horner.Real.finiteModulus saved.receipt.selection.depth)
    saved.left saved.leftBank input.accuracy

set_option genInjectivity false in
/-- The actual fresh comparison, reused saved comparison or certified saved-frontier refinement. -/
inductive SourceProgress (chosen : Chosen input) : Runner.Saved input.retained input.right → Type where
  /-- Both original stage constructions supplied this actual common comparison. -/ | fresh
      (comparison : StageComparison.Compared (selectedRequest input chosen.selected) input.right) :
      SourceProgress chosen
        (Runner.Saved.ofCompared input.retained chosen.selected.val input.accuracy input.right comparison)
  /-- A new left stage was compared against the actual retained right frontier and bank. -/ | changed
      (saved : Runner.Saved input.retained input.right) (present : saved ∈ input.saved)
      (different : saved.receipt.index ≠ chosen.selected.val.index)
      (stage : Source.Result policy schedule extraDepth chosen.selected.val.index input.accuracy)
      (common : Comparison.Observation.Certified
        (StageComparison.retainedFrontier (selectedRequest input chosen.selected) stage) saved.rightFrontier) :
      SourceProgress chosen (saved.afterStage chosen.selected.val input.accuracy stage common)
  /-- The supplied saved comparison was already adequate for this request. -/ | reused
      (saved : Runner.Saved input.retained input.right) (present : saved ∈ input.saved)
      (same : saved.receipt = chosen.selected.val)
      (adequate : (integralBound saved.left.cells).width < input.accuracy.tolerance) : SourceProgress chosen saved
  /-- The supplied saved frontier and point bank produced this actual refined comparison. -/ | refined
      (saved : Runner.Saved input.retained input.right) (present : saved ∈ input.saved)
      (same : saved.receipt = chosen.selected.val) (step : SavedStep input saved)
      (common : Comparison.Observation.Certified step.val.frontier saved.rightFrontier) :
      SourceProgress chosen (saved.afterContinuation step.val common)

/-- Detect whether this branch returned an already retained saved comparison. -/
@[expose] def SourceProgress.reuses (chosen : Chosen input) :
    {comparison : Runner.Saved input.retained input.right} → SourceProgress input chosen comparison → Bool
  | _, .reused _ _ _ _ => true
  | _, _ => false

set_option genInjectivity false in
/-- The actual runner, selected receipt, retained source frontiers and common comparison. -/
structure Result extends Chosen input where
  /-- The actual retained source frontiers, banks and common comparison. -/ comparison :
    Runner.Saved input.retained input.right
  /-- The actual fresh, reuse or refinement branch that produced the retained comparison. -/ progress :
    SourceProgress input toChosen comparison
  /-- Its original receipt belongs to the same selected stage as the returned model receipt. -/ comparison_receipt :
    comparison.receipt = selected.val
  /-- The actual left frontier meets this request's accuracy. -/ accurate :
    (integralBound comparison.left.cells).width < input.accuracy.tolerance

/-- Each displayed model or source question is answered from its exact returned owner. -/
@[expose] def originalReply : Question input → Reply input
  | .inl index => .inl (Model.originalReply input.retained index)
  | .inr ⟨selected, .fresh question⟩ =>
      .inr ⟨selected, .fresh (StageComparison.originalReply (selectedRequest input selected) input.right question)⟩
  | .inr ⟨selected, .refine question⟩ =>
      .inr ⟨selected, .refine (Continuation.originalReplyAll
        (selectedPreparation selected.val.selection input.accuracy) question)⟩
  | .inr ⟨selected, .common question⟩ =>
      .inr ⟨selected, .common (Comparison.Observation.originalReply
        (selectedRequest input selected).source input.right.source question)⟩

/-- Display one actual model cache miss, retaining a wrong operation as an absent receipt. -/
private def modelHandler (index : Nat) :
    Program (Question input) (Reply input) (Except Empty (Option (Model.Receipt input.retained))) :=
  .request (.inl index) fun reply => match reply with
    | .inl receipt => .pure (.ok (some receipt))
    | .inr _ => .pure (.ok none)

/-- Observe original model queries through the caller's actual retained receipt bank. -/
def modelProgram : Program (Question input) (Reply input)
    (Except Empty (Basic.Execution Nat (Option (Model.Receipt input.retained))
      (Except (Program.Certified.Cache.Failure (Model.receiptSource input.retained)) (CachedExecution input)))) :=
  Program.substituteChecked (modelHandler input)
    (Program.Certified.Cache.computation (Model.receiptSource input.retained) input.receiptBank input.modelProgram)

/-- Original replies preserve the complete cached model execution and its updated receipt bank. -/
private theorem modelProgram_original :
    ((modelProgram input).protocol.run (originalReply input)).value =
      .ok ((Program.protocol
        (Program.Certified.Cache.computation (Model.receiptSource input.retained) input.receiptBank
          input.modelProgram)).run (fun index => some (Model.originalReply input.retained index))) := by
  unfold modelProgram
  apply Program.substituteChecked_value
  intro index
  rfl

/-- Display one fresh-stage source question and reject any other operation. -/
private def sourceHandler (completed : CachedExecution input) (recorded : Recorded input) (selected : Selected input)
    (question : StageComparison.Question (selectedRequest input selected) input.right) :
    Program (Question input) (Reply input)
      (Except (Failure input) (StageComparison.Reply (selectedRequest input selected) input.right)) :=
  .request (.inr ⟨selected, .fresh question⟩) fun reply => match reply with
    | .inr ⟨reported, .fresh response⟩ => by
        have same : reported = selected := Subtype.ext (reported.property.trans selected.property.symm)
        cases same
        exact .pure (.ok response)
    | _ => .pure (.error (.sourceOperation completed recorded ⟨selected, .fresh question⟩))

/-- Original fresh-stage replies preserve the actual selected owner and source question. -/
private theorem sourceHandler_original (completed : CachedExecution input) (recorded : Recorded input)
    (selected : Selected input) (question : StageComparison.Question (selectedRequest input selected) input.right) :
    ((sourceHandler input completed recorded selected question).protocol.run (originalReply input)).value =
      .ok (StageComparison.originalReply (selectedRequest input selected) input.right question) := by
  rfl

/-- Run the fresh source comparison using the actual selected receipt returned by the model requests. -/
def sourceProgram (completed : CachedExecution input) (recorded : Recorded input) (selected : Selected input) :
    Program (Question input) (Reply input) (Except (Failure input)
      (Basic.Execution (StageComparison.Question (selectedRequest input selected) input.right)
        (StageComparison.Reply (selectedRequest input selected) input.right)
        (Except (StageComparison.Failure (selectedRequest input selected) input.right)
          (StageComparison.Compared (selectedRequest input selected) input.right)))) :=
  (StageComparison.computation (selectedRequest input selected) input.right).substituteChecked
    (sourceHandler input completed recorded selected)

/-- Original fresh replies preserve the complete selected-stage comparison and its source log. -/
theorem sourceProgram_original (completed : CachedExecution input) (recorded : Recorded input)
    (selected : Selected input) :
    ((sourceProgram input completed recorded selected).protocol.run (originalReply input)).value =
      .ok ((StageComparison.computation (selectedRequest input selected) input.right).protocol.run
        (StageComparison.originalReply (selectedRequest input selected) input.right)) := by
  unfold sourceProgram
  apply Program.substituteChecked_value
  intro question
  exact sourceHandler_original input completed recorded selected question

/-- The saved receipt itself is a selected owner whenever its original index matches the returned receipt. -/
@[expose] def savedSelected (saved : Runner.Saved input.retained input.right) (selected : Selected input)
    (same : saved.receipt = selected.val) : Selected input := ⟨saved.receipt, same.trans selected.property⟩

/-- Display one original left-frontier continuation question at the actual saved source owner. -/
private def refineHandler (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (question : Continuation.Query (selectedPreparation saved.receipt.selection input.accuracy)) :
    Program (Question input) (Reply input) (Except (Failure input)
      (SourcePoint (Horner.Real.finiteSource saved.receipt.selection.depth))) :=
  let owner := savedSelected input saved selected same
  .request (.inr ⟨owner, .refine question⟩) fun reply => match reply with
    | .inr ⟨reported, .refine response⟩ => by
        have equal : reported = owner := Subtype.ext (reported.property.trans owner.property.symm)
        cases equal
        exact .pure (.ok response)
    | _ => .pure (.error (.sourceOperation completed recorded ⟨owner, .refine question⟩))

/-- Original continuation replies preserve the actual saved source owner. -/
private theorem refineHandler_original (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (question : Continuation.Query (selectedPreparation saved.receipt.selection input.accuracy)) :
    ((refineHandler input completed recorded saved selected same question).protocol.run (originalReply input)).value =
      .ok (Continuation.originalReplyAll (selectedPreparation saved.receipt.selection input.accuracy) question) := by
  rfl

/-- Continue the actual saved left frontier through its cache-aware original source observer. -/
def refineProgram (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input)
    (same : saved.receipt = selected.val) :=
  (Continuation.certifiedComputation (Horner.Real.finiteModulus saved.receipt.selection.depth)
    saved.left saved.leftBank input.accuracy).substituteChecked
      (refineHandler input completed recorded saved selected same)

/-- Original continuation replies recover the complete saved-frontier source execution. -/
theorem refineProgram_original (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input)
    (same : saved.receipt = selected.val) :
    ((refineProgram input completed recorded saved selected same).protocol.run (originalReply input)).value =
      .ok ((Continuation.certifiedComputation (Horner.Real.finiteModulus saved.receipt.selection.depth)
        saved.left saved.leftBank input.accuracy).protocol.run
          (Continuation.originalReplyAll (selectedPreparation saved.receipt.selection input.accuracy))) := by
  unfold refineProgram
  apply Program.substituteChecked_value
  intro question
  exact refineHandler_original input completed recorded saved selected same question

/-- Display one common-point cache miss with the same saved source owners. -/
private def commonHandler (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (question : Comparison.Observation.Query) :
    Program (Question input) (Reply input) (Except (Failure input)
      (Comparison.Observation.Reply (Horner.Real.finiteSource saved.receipt.selection.depth) input.right.source)) :=
  let owner := savedSelected input saved selected same
  .request (.inr ⟨owner, .common question⟩) fun reply => match reply with
    | .inr ⟨reported, .common response⟩ => by
        have equal : reported = owner := Subtype.ext (reported.property.trans owner.property.symm)
        cases equal
        exact .pure (.ok response)
    | _ => .pure (.error (.sourceOperation completed recorded ⟨owner, .common question⟩))

/-- Original common-point replies preserve the two actual saved source owners. -/
private theorem commonHandler_original (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (question : Comparison.Observation.Query) :
    ((commonHandler input completed recorded saved selected same question).protocol.run (originalReply input)).value =
      .ok (Comparison.Observation.originalReply (Horner.Real.finiteSource saved.receipt.selection.depth)
        input.right.source question) := by
  rfl

/-- Compare the actual continued left frontier with the retained right frontier using both saved banks. -/
def commonProgram (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (step : Producer.Continuation (producer (Horner.Real.finiteModulus saved.receipt.selection.depth)) saved.left) :=
  (Cache.computation (saved.continuationBank step) saved.rightBank step.frontier
    saved.rightFrontier).substituteChecked (commonHandler input completed recorded saved selected same)

/-- Original common replies recover the complete cached comparison at the actual continued frontier. -/
theorem commonProgram_original (completed : CachedExecution input) (recorded : Recorded input)
    (saved : Runner.Saved input.retained input.right) (selected : Selected input) (same : saved.receipt = selected.val)
    (step : Producer.Continuation (producer (Horner.Real.finiteModulus saved.receipt.selection.depth)) saved.left) :
    ((commonProgram input completed recorded saved selected same step).protocol.run (originalReply input)).value =
      .ok ((Cache.computation (saved.continuationBank step) saved.rightBank step.frontier
        saved.rightFrontier).protocol.run (Comparison.Observation.originalReply
          (Horner.Real.finiteSource saved.receipt.selection.depth) input.right.source)) := by
  unfold commonProgram
  apply Program.substituteChecked_value
  intro question
  exact commonHandler_original input completed recorded saved selected same question

/-- Build the chosen runner data from the exact returned receipt execution. -/
@[expose] def Chosen.ofExecution (completed : CachedExecution input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) : Chosen input :=
  let recorded := Model.receiptRecord input.retained input.request input.count completed.execution observation success
  let selected : Selected input :=
    ⟨Model.selectedReceipt input.retained input.request input.count completed.execution observation success,
      Model.selectedReceipt_original input.retained input.request input.count completed.execution observation success⟩
  ⟨completed, recorded, success, selected, rfl,
    Model.selectedReceipt_model input.retained input.request input.count completed.execution observation success⟩

/-- Construct both original source stages when no suitable saved comparison exists. -/
@[expose] def freshProgram (chosen : Chosen input) : Program (Question input) (Reply input)
    (Except (Failure input) (Result input)) :=
  (sourceProgram input chosen.completed chosen.recorded chosen.selected).map fun sourceResult =>
    match sourceResult with
    | .error failure => .error failure
    | .ok sourceExecution => match sourceExecution.value with
      | .error failure => .error (.source chosen.completed chosen.recorded chosen.selected failure)
      | .ok comparison =>
          let saved := Runner.Saved.ofCompared input.retained chosen.selected.val input.accuracy input.right comparison
          .ok ⟨chosen, saved, .fresh comparison, rfl,
            Runner.Saved.ofCompared_accurate input.retained chosen.selected.val input.accuracy input.right comparison⟩

/-- Construct only the newly selected left stage through its actual source requests. -/
def changedLeftProgram (chosen : Chosen input) :=
  (StageComparison.leftProgram (selectedRequest input chosen.selected) input.right).substituteChecked
    (sourceHandler input chosen.completed chosen.recorded chosen.selected)

/-- Original replies recover the complete newly selected left-stage execution. -/
theorem changedLeftProgram_original (chosen : Chosen input) :
    ((changedLeftProgram input chosen).protocol.run (originalReply input)).value =
      .ok ((StageComparison.leftProgram (selectedRequest input chosen.selected) input.right).protocol.run
        (StageComparison.originalReply (selectedRequest input chosen.selected) input.right)) := by
  unfold changedLeftProgram
  apply Program.substituteChecked_value
  intro question
  exact sourceHandler_original input chosen.completed chosen.recorded chosen.selected question

/-- Display an actual common-point miss for the new left and retained right source owners. -/
private def changedCommonHandler (chosen : Chosen input) (question : Comparison.Observation.Query) :
    Program (Question input) (Reply input) (Except (Failure input)
      (Comparison.Observation.Reply (selectedRequest input chosen.selected).source input.right.source)) :=
  .request (.inr ⟨chosen.selected, .common question⟩) fun reply => match reply with
    | .inr ⟨reported, .common response⟩ => by
        have equal : reported = chosen.selected := Subtype.ext (reported.property.trans chosen.selected.property.symm)
        cases equal
        exact .pure (.ok response)
    | _ => .pure (.error (.sourceOperation chosen.completed chosen.recorded ⟨chosen.selected, .common question⟩))

/-- Original common-point replies retain the actual newly selected and saved source owners. -/
private theorem changedCommonHandler_original (chosen : Chosen input) (question : Comparison.Observation.Query) :
    ((changedCommonHandler input chosen question).protocol.run (originalReply input)).value =
      .ok (Comparison.Observation.originalReply (selectedRequest input chosen.selected).source input.right.source
        question) := by
  rfl

/-- Compare a new left frontier with the original saved right frontier and its retained point bank. -/
def changedCommonProgram (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (stage : Source.Result policy schedule extraDepth chosen.selected.val.index input.accuracy) :=
  let left := StageComparison.retainedFrontier (selectedRequest input chosen.selected) stage
  (Cache.computation (left.cells.map fun cell => cell.item) saved.rightBank
    left saved.rightFrontier).substituteChecked (changedCommonHandler input chosen)

/-- Original replies return the complete common comparison with the unchanged saved right frontier. -/
theorem changedCommonProgram_original (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (stage : Source.Result policy schedule extraDepth chosen.selected.val.index input.accuracy) :
    let left := StageComparison.retainedFrontier (selectedRequest input chosen.selected) stage
    ((changedCommonProgram input chosen saved stage).protocol.run (originalReply input)).value =
      .ok ((Cache.computation (left.cells.map fun cell => cell.item) saved.rightBank
        left saved.rightFrontier).protocol.run (Comparison.Observation.originalReply
          (selectedRequest input chosen.selected).source input.right.source)) := by
  unfold changedCommonProgram
  apply Program.substituteChecked_value
  intro question
  exact changedCommonHandler_original input chosen question

/-- Build a new left stage while retaining the actual earlier right stage and common-point bank. -/
@[expose] def changedProgram (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (present : saved ∈ input.saved) (different : saved.receipt.index ≠ chosen.selected.val.index) :
    Program (Question input) (Reply input) (Except (Failure input) (Result input)) :=
  (changedLeftProgram input chosen).bind fun first => match first with
    | .error failure => .pure (.error failure)
    | .ok execution => match execution.value with
      | .error invalid => .pure (.error (.source chosen.completed chosen.recorded chosen.selected invalid))
      | .ok stage =>
          (changedCommonProgram input chosen saved stage).map fun second => match second with
            | .error failure => .error failure
            | .ok execution => match execution.value with
              | .error invalid => .error (.changedCommon chosen.completed chosen.recorded saved chosen.selected
                  stage invalid)
              | .ok common =>
                  .ok ⟨chosen, saved.afterStage chosen.selected.val input.accuracy stage common,
                    .changed saved present different stage common, rfl,
                    saved.afterStage_accurate chosen.selected.val input.accuracy stage common⟩

/-- Reuse an adequate saved comparison or continue its actual source frontier for a tighter request. -/
@[expose] def savedProgram (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (present : saved ∈ input.saved) (same : saved.receipt = chosen.selected.val) :
    Program (Question input) (Reply input) (Except (Failure input) (Result input)) := by
  if adequate : (integralBound saved.left.cells).width < input.accuracy.tolerance then
    exact .pure (.ok ⟨chosen, saved, .reused saved present same adequate, same, adequate⟩)
  else
    exact (refineProgram input chosen.completed chosen.recorded saved chosen.selected same).bind fun first =>
      match first with
      | .error failure => .pure (.error failure)
      | .ok execution => match execution.value with
        | .error invalid => .pure (.error (.refine chosen.completed chosen.recorded saved invalid))
        | .ok certified =>
            (commonProgram input chosen.completed chosen.recorded saved chosen.selected same certified.val).map
              fun second => match second with
                | .error failure => .error failure
                | .ok execution => match execution.value with
                  | .error invalid => .error (.common chosen.completed chosen.recorded saved certified.val invalid)
                  | .ok common => by
                      have sameRequest : certified.val.request = input.accuracy :=
                        (congrArg (fun step => step.request) certified.property).trans
                          (Producer.advanceCached_request _ _ _ _)
                      let width := (integralBound certified.val.frontier.cells).width
                      have toleranceEq : certified.val.request.tolerance = input.accuracy.tolerance :=
                        congrArg AccuracyRequest.tolerance sameRequest
                      have accurate : width < input.accuracy.tolerance :=
                        Eq.mp (congrArg (fun tolerance : Fraction.Rational => width < tolerance) toleranceEq)
                          certified.val.accurate
                      exact .ok ⟨chosen, saved.afterContinuation certified.val common,
                        .refined saved present same certified common, same, accurate⟩

/-- An adequate saved comparison is returned unchanged without a source request. -/
theorem savedProgram_reused (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (present : saved ∈ input.saved) (same : saved.receipt = chosen.selected.val)
    (adequate : (integralBound saved.left.cells).width < input.accuracy.tolerance)
    (oracle : Question input → Reply input) :
    ((savedProgram input chosen saved present same).protocol.run oracle).value =
      .ok ⟨chosen, saved, .reused saved present same adequate, same, adequate⟩ ∧
      ((savedProgram input chosen saved present same).protocol.run oracle).trace = [] := by
  unfold savedProgram
  rw [dif_pos adequate]
  exact ⟨rfl, rfl⟩

/-- Prefer an adequate saved comparison, then refine a matching stage or retain the latest right source. -/
@[expose] def comparisonProgram (chosen : Chosen input) : Program (Question input) (Reply input)
    (Except (Failure input) (Result input)) :=
  match Runner.Saved.findAdequate chosen.selected.val.index input.accuracy input.saved with
  | some found =>
      savedProgram input chosen found.val found.property.1
        (Model.Receipt.eq_of_index found.val.receipt chosen.selected.val found.property.2.1)
  | none =>
      match Runner.Saved.findStage chosen.selected.val.index input.saved with
      | some found =>
          savedProgram input chosen found.val found.property.1
            (Model.Receipt.eq_of_index found.val.receipt chosen.selected.val found.property.2)
      | none =>
          match present : input.saved with
          | [] => freshProgram input chosen
          | saved :: remaining =>
              let member : saved ∈ input.saved := present.symm ▸ List.Mem.head remaining
              if same : saved.receipt.index = chosen.selected.val.index then
                savedProgram input chosen saved member
                  (Model.Receipt.eq_of_index saved.receipt chosen.selected.val same)
              else changedProgram input chosen saved member same

/-- Run the original model requests, then reuse or continue the actual saved source comparison. -/
@[expose] def computation : Program (Question input) (Reply input) (Except (Failure input) (Result input)) :=
  (modelProgram input).bind fun modelResult =>
    match modelResult with
    | .error impossible => nomatch impossible
    | .ok modelExecution =>
        match modelExecution.value with
        | .error invalid => .pure (.error (.model invalid))
        | .ok completed =>
            match success : completed.execution.val.value with
            | .error failure => .pure (.error (.runner completed failure success))
            | .ok observation => comparisonProgram input (Chosen.ofExecution input completed observation success)

/-- Continue from the actual returned model bank and source comparison on the same original owners. -/
@[expose] def Result.continuation (result : Result input) (request : CertifiedProgram.Request)
    (count : Nat) (accuracy : AccuracyRequest) :
    Input policy rightPolicy schedule rightSchedule extraDepth rightExtra :=
  let saved := if SourceProgress.reuses input result.toChosen result.progress then input.saved
    else result.comparison :: input.saved
  ⟨input.retained, result.completed.bank, request, count, accuracy, input.right, saved⟩

/-- The returned comparison bounds the exact selected sample in the returned runner record. -/
theorem Result.selected_difference_le_actual (result : Result input) :
    Fraction.abs (result.recorded.observation.selected.sample.re - input.right.stage.sample.re) ≤
      (integralBound result.comparison.left.cells).width +
        (integralBound result.comparison.rightFrontier.cells).width + result.comparison.common.val.pointBudget := by
  have sample_eq : result.recorded.observation.selected.sample = result.selected.val.model.sample :=
    (Runner.selected_sample result.recorded).trans (congrArg (fun model => model.sample) result.selected_model.symm)
  have savedModel := congrArg (fun receipt => receipt.model.sample) result.comparison_receipt
  rw [sample_eq, ← savedModel]
  exact result.comparison.samples_difference_le

/-- The actual returned sample is the approximation sample of its retained source anchor.

The index belongs to the same returned model receipt as the anchor. This
identity uses the original model and program retained by the comparison.
-/
theorem Result.selected_sample_approximation (result : Result input) :
    result.recorded.observation.selected.sample =
      result.comparison.leftAnchor.program.approximation.sample result.comparison.receipt.index := by
  have sameModel : result.comparison.leftAnchor.stage = result.selected.val.model :=
    result.comparison.leftModel.trans (congrArg (fun receipt => receipt.model) result.comparison_receipt)
  have selected : result.recorded.observation.selected.sample = result.comparison.leftAnchor.stage.sample :=
    (Runner.selected_sample result.recorded).trans
      ((congrArg (fun model => model.sample) result.selected_model.symm).trans
        (congrArg (fun model => model.sample) sameModel.symm))
  rw [result.comparison.leftAnchor.stage_eq] at selected
  exact selected

/-- The actual selected runner sample is its retained finite Taylor sample minus one. -/
theorem Result.selected_sample_taylor (result : Result input) :
    result.recorded.observation.selected.sample =
      Horner.Sample.sample 1 (result.selected.val.selection.depth + 1) - 1 := by
  calc
    _ = result.selected.val.model.sample :=
      (Runner.selected_sample result.recorded).trans
        (congrArg (fun model => model.sample) result.selected_model.symm)
    _ = (result.selected.val.selection.snapshot extraDepth).sample :=
      congrArg (fun model => model.sample) (selected_model_eq_snapshot input result.selected)
    _ = _ := Selection.snapshot_sample result.selected.val.selection extraDepth

/-- The retained source anchor's output name agrees with the existing exponential-minus-one name.

This is an operational comparison of the two names at later finite requests;
it does not assign an arbitrary accuracy to this one selected sample.
-/
def Result.output_equivalent_existing (result : Result input) :
    Gaussian.Equivalence.NamedEquivalent result.comparison.leftAnchor.program.output.name
      Equivalence.Reference.exponentialMinusOne := by
  rw [result.comparison.leftAnchor.program_eq]
  exact Equivalence.Existing.output_equivalent_existing policy schedule extraDepth

/-- The original runner records with the same owner, request and count are equal. -/
private theorem recorded_unique (first second : Recorded input) : first = second := by
  have observation_eq : first.observation = second.observation :=
    Except.ok.inj (first.value_eq.symm.trans second.value_eq)
  have trace_eq : first.trace = second.trace := first.trace_eq.trans second.trace_eq.symm
  cases first with
  | mk firstObservation firstTrace firstValue firstTraceEq =>
    cases second with
    | mk secondObservation secondTrace secondValue secondTraceEq =>
      cases observation_eq
      cases trace_eq
      rfl

/-- Original replies return a fresh comparison attached to the same actual chosen runner. -/
private theorem freshProgram_original (chosen : Chosen input) :
    ∃ result : Result input, ((freshProgram input chosen).protocol.run (originalReply input)).value = .ok result ∧
      result.toChosen = chosen := by
  unfold freshProgram
  rw [Program.map_execution, Protocol.map_run_value, sourceProgram_original]
  dsimp only
  rw [StageComparison.computation_original]
  exact ⟨_, rfl, rfl⟩

/-- Original replies construct the new left stage and its comparison with the saved right frontier. -/
private theorem changedProgram_original (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (present : saved ∈ input.saved) (different : saved.receipt.index ≠ chosen.selected.val.index) :
    ∃ result : Result input, ((changedProgram input chosen saved present different).protocol.run
      (originalReply input)).value = .ok result ∧ result.toChosen = chosen := by
  unfold changedProgram
  rw [Program.bind_execution, Protocol.bind_run_value, changedLeftProgram_original]
  dsimp only
  rw [StageComparison.leftProgram_original]
  rw [Program.map_execution, Protocol.map_run_value, changedCommonProgram_original]
  dsimp only
  rw [Cache.computation_original]
  exact ⟨_, rfl, rfl⟩

/-- Original replies preserve a saved comparison or return its actual refined successor. -/
private theorem savedProgram_original (chosen : Chosen input) (saved : Runner.Saved input.retained input.right)
    (present : saved ∈ input.saved) (same : saved.receipt = chosen.selected.val) :
    ∃ result : Result input, ((savedProgram input chosen saved present same).protocol.run (originalReply input)).value =
      .ok result ∧ result.toChosen = chosen := by
  unfold savedProgram
  by_cases adequate : (integralBound saved.left.cells).width < input.accuracy.tolerance
  · rw [dif_pos adequate]
    exact ⟨_, rfl, rfl⟩
  · rw [dif_neg adequate, Program.bind_execution, Protocol.bind_run_value, refineProgram_original]
    dsimp only
    have refined := Continuation.certifiedComputation_original
      (Horner.Real.finiteModulus saved.receipt.selection.depth) saved.left saved.leftBank input.accuracy
    change ((Continuation.certifiedComputation (Horner.Real.finiteModulus saved.receipt.selection.depth)
      saved.left saved.leftBank input.accuracy).protocol.run
        (Continuation.originalReplyAll (selectedPreparation saved.receipt.selection input.accuracy))).value = _
      at refined
    rw [refined]
    rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
    dsimp only
    rw [Cache.computation_original]
    exact ⟨_, rfl, rfl⟩

/-- Original replies return an actual chosen result in every saved or fresh comparison branch. -/
private theorem comparisonProgram_original (chosen : Chosen input) :
    ∃ result : Result input, ((comparisonProgram input chosen).protocol.run (originalReply input)).value =
      .ok result ∧ result.toChosen = chosen := by
  unfold comparisonProgram
  split
  · rename_i found foundEq
    exact savedProgram_original input chosen found.val found.property.1
      (Model.Receipt.eq_of_index found.val.receipt chosen.selected.val found.property.2.1)
  · split
    · rename_i found foundEq
      exact savedProgram_original input chosen found.val found.property.1
        (Model.Receipt.eq_of_index found.val.receipt chosen.selected.val found.property.2)
    · split
      · exact freshProgram_original input chosen
      · rename_i saved remaining present
        by_cases same : saved.receipt.index = chosen.selected.val.index
        · rw [dif_pos same]
          exact savedProgram_original input chosen saved (present.symm ▸ List.Mem.head remaining)
            (Model.Receipt.eq_of_index saved.receipt chosen.selected.val same)
        · rw [dif_neg same]
          exact changedProgram_original input chosen saved (present.symm ▸ List.Mem.head remaining) same

/-- Original replies return the original runner and its actual retained source comparison. -/
theorem computation_original :
    ∃ result : Result input,
      ((computation input).protocol.run (originalReply input)).value = .ok result ∧
      result.recorded = Record.record input.retained.program input.request input.count := by
  let original := Record.record input.retained.program input.request input.count
  have runnerValue : (input.modelProgram.protocol.run input.retained.program.stage).value =
      .ok original.observation := by
    change ((Expansion.program (control input.retained.program) input.request input.count).protocol.run
      input.retained.program.stage).value = _
    rw [Expansion.program_execution]
    exact original.value_eq
  obtain ⟨completed, returned⟩ := Program.Certified.Cache.computation_original
    (Model.receiptSource input.retained) (Model.originalReply input.retained) (fun _ => rfl)
    input.modelProgram input.receiptBank
  have projectedValue : (Model.projectExecution input.retained completed.execution).val.value =
      .ok original.observation := by
    exact (congrArg Basic.Execution.value
      (Model.projectExecution input.retained completed.execution).property).trans runnerValue
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, modelProgram_original]
  dsimp only
  rw [returned]
  dsimp only
  split
  next failure failed =>
    have impossible : Except.error failure = Except.ok original.observation := failed.symm.trans projectedValue
    cases impossible
  next observation success =>
    obtain ⟨result, value, chosen⟩ := comparisonProgram_original input
      (Chosen.ofExecution input completed observation success)
    rw [value]
    refine ⟨result, rfl, ?_⟩
    have recordEq := congrArg Chosen.recorded chosen
    exact recordEq.trans (recorded_unique input _ original)

/-- Replaying any actual combined trace returns its complete original success or typed failure. -/
theorem computation_replay (oracle : Question input → Reply input) :
    (computation input).protocol.replayExact ((computation input).protocol.run oracle).trace =
      .ok ((computation input).protocol.run oracle).value :=
  (computation input).protocol.replayExact_run oracle

/-- Changes outside the actual combined model-and-source trace preserve its complete execution. -/
theorem payload_erasure {Payload : Type} (oracle : Question input → Reply input) (payload : Payload)
    (outside : Payload → Question input → Reply input) :
    (computation input).protocol.run (Boundary.Trace.overlay
      ((computation input).protocol.run oracle).trace (outside payload)) = (computation input).protocol.run oracle :=
  (computation input).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Full

end
