module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Model
import Purelib.Data.List.Membership

/-!
# Retained exponential source comparison

A saved comparison retains its original stage receipts, current source
frontiers and point banks, and the common readings on those exact frontiers.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Data.List
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.SourceFrontier
open Purelib.Integration.SourceFrontier.Continuous

set_option genInjectivity false in
/-- The original stage owners, current source frontiers and their actual common observations. -/
structure Saved {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (retained : Program.Retained policy schedule extraDepth)
    (right : StageComparison.Request rightPolicy rightSchedule rightExtra) where
  /-- The actual receipt of the left original model request. -/ receipt : Model.Receipt retained
  /-- The original accuracy request for the left source anchor. -/ leftRequest : AccuracyRequest
  /-- The returned source-linked result for the left original stage. -/ leftAnchor :
    Source.Result policy schedule extraDepth receipt.index leftRequest
  /-- That anchor retains the same original model. -/ leftModel : leftAnchor.stage = receipt.model
  /-- The actual current left frontier at the receipt's own selected Taylor depth. -/ left :
    SourceFrontier (Horner.Real.finiteSource receipt.selection.depth)
  /-- The retained left frontier admits the same original model sample. -/ leftInside :
    (integralBound left.cells).Contains receipt.model.sample.re
  /-- Actual saved point observations at the left source owner. -/ leftBank :
    List (SourcePoint (Horner.Real.finiteSource receipt.selection.depth))
  /-- The returned source-linked result for the right original stage. -/ rightAnchor :
    Source.Result rightPolicy rightSchedule rightExtra right.index right.accuracy
  /-- That anchor retains the same original right model. -/ rightModel : rightAnchor.stage = right.stage
  /-- The actual current right frontier at the same original right source owner. -/ rightFrontier :
    SourceFrontier right.source
  /-- The retained right frontier admits the same original right model sample. -/ rightInside :
    (integralBound rightFrontier.cells).Contains right.stage.sample.re
  /-- Actual saved point observations at the right source owner. -/ rightBank : List (SourcePoint right.source)
  /-- The actual common readings of these two current frontiers. -/ common :
    Comparison.Observation.Certified left rightFrontier

namespace Saved

/-- Extend the supplied receipt bank with original saved-stage receipts absent by stage index.

The supplied bank retains precedence. Saved comparisons are visited in their
original order, and a receipt already represented by that index is not added.
-/
@[expose] def mergeReceipts {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} :
    List (Model.Receipt retained) → List (Saved retained right) → List (Model.Receipt retained)
  | bank, [] => bank
  | bank, saved :: remaining =>
      if bank.any (fun receipt => receipt.index.beq saved.receipt.index) then mergeReceipts bank remaining
      else mergeReceipts (bank ++ [saved.receipt]) remaining

/-- The caller's complete supplied receipt bank remains the exact prefix of the merged bank. -/
theorem mergeReceipts_prefix {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra}
    (entries : List (Saved retained right)) : ∀ bank : List (Model.Receipt retained),
      ∃ added, mergeReceipts bank entries = bank ++ added := by
  induction entries with
  | nil =>
      intro bank
      exact ⟨[], (List.append_nil bank).symm⟩
  | cons saved remaining induction =>
      intro bank
      change ∃ added, (if bank.any (fun receipt => receipt.index.beq saved.receipt.index) then
        mergeReceipts bank remaining else mergeReceipts (bank ++ [saved.receipt]) remaining) = bank ++ added
      cases found : bank.any (fun receipt => receipt.index.beq saved.receipt.index) with
      | false =>
          obtain ⟨added, same⟩ := induction (bank ++ [saved.receipt])
          exact ⟨[saved.receipt] ++ added, same.trans (List.append_assoc bank [saved.receipt] added)⟩
      | true => exact induction bank

/-- A positive finite index search identifies an actual receipt in its original bank. -/
private theorem bank_index_witness {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} (index : Nat) (bank : List (Model.Receipt retained)) :
    bank.any (fun receipt => receipt.index.beq index) = true → ∃ receipt ∈ bank, receipt.index = index := by
  induction bank with
  | nil =>
      intro found
      cases found
  | cons receipt remaining induction =>
      intro found
      change ((receipt.index.beq index) || remaining.any (fun item => item.index.beq index)) = true at found
      cases same : receipt.index.beq index with
      | true => exact ⟨receipt, List.Mem.head remaining, Nat.eq_of_beq_eq_true same⟩
      | false =>
          rw [same] at found
          obtain ⟨later, member, equal⟩ := induction found
          exact ⟨later, List.Mem.tail receipt member, equal⟩

/-- A merged bank preserves every actual receipt supplied in its original caller bank. -/
theorem mergeReceipts_retains {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra}
    (entries : List (Saved retained right)) (bank : List (Model.Receipt retained))
    {receipt : Model.Receipt retained} (member : receipt ∈ bank) : receipt ∈ mergeReceipts bank entries := by
  obtain ⟨added, same⟩ := mergeReceipts_prefix entries bank
  rw [same]
  exact Membership.mem_append.mpr (Or.inl member)

/-- Every original saved comparison's receipt is represented in the merged model bank.

A caller receipt at the same stage retains precedence. Its original-owner
certificate makes it equal to that saved stage's receipt.
-/
theorem mergeReceipts_contains {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra}
    (entries : List (Saved retained right)) : ∀ (bank : List (Model.Receipt retained))
      (saved : Saved retained right), saved ∈ entries → saved.receipt ∈ mergeReceipts bank entries := by
  induction entries with
  | nil =>
      intro _ _ member
      cases member
  | cons first remaining induction =>
      intro bank saved member
      change saved.receipt ∈ (if bank.any (fun receipt => receipt.index.beq first.receipt.index) then
        mergeReceipts bank remaining else mergeReceipts (bank ++ [first.receipt]) remaining)
      cases found : bank.any (fun receipt => receipt.index.beq first.receipt.index) with
      | false =>
          cases member with
          | head =>
              apply mergeReceipts_retains remaining (bank ++ [first.receipt])
              exact Membership.mem_append.mpr (Or.inr (List.Mem.head []))
          | tail _ present => exact induction (bank ++ [first.receipt]) saved present
      | true =>
          cases member with
          | head =>
              obtain ⟨receipt, present, sameIndex⟩ := bank_index_witness first.receipt.index bank found
              have same := Model.Receipt.eq_of_index receipt first.receipt sameIndex
              rw [← same]
              exact mergeReceipts_retains remaining bank present
          | tail _ present => exact induction bank saved present

/-- Find the first saved comparison for the supplied original stage index. -/
@[expose] def findStage {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (index : Nat) :
    (entries : List (Saved retained right)) →
      Option {saved : Saved retained right // saved ∈ entries ∧ saved.receipt.index = index}
  | [] => none
  | first :: remaining =>
      if same : first.receipt.index = index then some ⟨first, List.Mem.head remaining, same⟩
      else match findStage index remaining with
        | none => none
        | some found => some ⟨found.val, List.Mem.tail first found.property.1, found.property.2⟩

/-- Find the first saved comparison whose original stage and actual frontier meet the request. -/
@[expose] def findAdequate {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (index : Nat) (request : AccuracyRequest) :
    (entries : List (Saved retained right)) → Option {saved : Saved retained right // saved ∈ entries ∧
      saved.receipt.index = index ∧ (integralBound saved.left.cells).width < request.tolerance}
  | [] => none
  | first :: remaining =>
      if same : first.receipt.index = index then
        if adequate : (integralBound first.left.cells).width < request.tolerance then
          some ⟨first, List.Mem.head remaining, same, adequate⟩
        else match findAdequate index request remaining with
          | none => none
          | some found => some ⟨found.val, List.Mem.tail first found.property.1, found.property.2⟩
      else match findAdequate index request remaining with
        | none => none
        | some found => some ⟨found.val, List.Mem.tail first found.property.1, found.property.2⟩

/-- The left request whose source and model belong to the actual retained receipt. -/
abbrev request {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right) :=
  StageComparison.Request.withSelected retained saved.receipt.index saved.receipt.selection saved.receipt.selection_eq
    saved.receipt.model saved.receipt.model_eq saved.leftRequest

/-- The original common readings pay for the two samples of their retained stage owners. -/
theorem samples_difference_le {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right) :
    Fraction.abs (saved.receipt.model.sample.re - right.stage.sample.re) ≤
      (integralBound saved.left.cells).width + (integralBound saved.rightFrontier.cells).width +
        saved.common.val.pointBudget :=
  saved.common.val.answers_difference_le saved.receipt.model.sample.re right.stage.sample.re
    saved.leftInside saved.rightInside

/-- Retain both returned stage anchors, their exact source frontiers and returned common readings. -/
@[expose] def ofCompared {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (retained : Program.Retained policy schedule extraDepth)
    (receipt : Model.Receipt retained) (request : AccuracyRequest)
    (right : StageComparison.Request rightPolicy rightSchedule rightExtra)
    (compared : StageComparison.Compared
      (StageComparison.Request.withSelected retained receipt.index receipt.selection receipt.selection_eq
        receipt.model receipt.model_eq request) right) : Saved retained right :=
  let leftRequest := StageComparison.Request.withSelected retained receipt.index receipt.selection receipt.selection_eq
    receipt.model receipt.model_eq request
  let left := StageComparison.retainedFrontier leftRequest compared.leftStage
  let rightFrontier := StageComparison.retainedFrontier right compared.rightStage
  { receipt := receipt
    leftRequest := request
    leftAnchor := compared.leftStage
    leftModel := StageComparison.Compared.left_stage leftRequest right compared
    left := left
    leftInside := by
      have inside := StageComparison.retainedFrontier_contains leftRequest compared.leftStage
      rw [StageComparison.Compared.left_stage leftRequest right compared] at inside
      exact inside
    leftBank := compared.common.val.readings.map CommonReading.leftPoint ++ left.cells.map (fun cell => cell.item)
    rightAnchor := compared.rightStage
    rightModel := StageComparison.Compared.right_stage leftRequest right compared
    rightFrontier := rightFrontier
    rightInside := by
      have inside := StageComparison.retainedFrontier_contains right compared.rightStage
      rw [StageComparison.Compared.right_stage leftRequest right compared] at inside
      exact inside
    rightBank := compared.common.val.readings.map CommonReading.rightPoint ++
      rightFrontier.cells.map (fun cell => cell.item)
    common := compared.common }

/-- Transporting a frontier between equal source owners preserves its integral width. -/
private theorem transport_width {source target : Fraction.Rational → Fraction.Rational} (same : source = target)
    (frontier : SourceFrontier source) :
    (integralBound (same ▸ frontier).cells).width = (integralBound frontier.cells).width := by
  cases same
  rfl

/-- A newly returned stage comparison meets its original left source request. -/
theorem ofCompared_accurate {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} (retained : Program.Retained policy schedule extraDepth)
    (receipt : Model.Receipt retained) (request : AccuracyRequest)
    (right : StageComparison.Request rightPolicy rightSchedule rightExtra)
    (compared : StageComparison.Compared
      (StageComparison.Request.withSelected retained receipt.index receipt.selection receipt.selection_eq
        receipt.model receipt.model_eq request) right) :
    (integralBound (ofCompared retained receipt request right compared).left.cells).width < request.tolerance := by
  let leftRequest := StageComparison.Request.withSelected retained receipt.index receipt.selection receipt.selection_eq
    receipt.model receipt.model_eq request
  change (integralBound (StageComparison.retainedFrontier leftRequest compared.leftStage).cells).width <
    request.tolerance
  unfold StageComparison.retainedFrontier
  rw [transport_width]
  have accurate := compared.leftStage.sourceResult.accurate
  rw [compared.leftStage.request_eq] at accurate
  exact accurate

/-- The original stage request supplied by one retained model receipt. -/
abbrev requestFor {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (receipt : Model.Receipt retained)
    (request : AccuracyRequest) :=
  StageComparison.Request.withSelected retained receipt.index receipt.selection receipt.selection_eq
    receipt.model receipt.model_eq request

/-- View a newly returned source frontier at the same retained receipt's selected source. -/
abbrev frontierFor {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (receipt : Model.Receipt retained)
    (request : AccuracyRequest) (stage : Source.Result policy schedule extraDepth receipt.index request) :=
  StageComparison.retainedFrontier (requestFor retained receipt request) stage

/-- The returned source stage retains the same original model as the supplied receipt. -/
theorem stage_model {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (receipt : Model.Receipt retained)
    (request : AccuracyRequest) (stage : Source.Result policy schedule extraDepth receipt.index request) :
    stage.stage = receipt.model :=
  stage.stage_eq.trans ((congrArg (fun program : Cached.Basic.CachedProgram => program.stage receipt.index)
    (stage.program_eq.trans retained.program_eq.symm)).trans receipt.model_eq.symm)

/-- The returned source frontier admits the sample retained in the original receipt. -/
theorem frontierFor_inside {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (receipt : Model.Receipt retained)
    (request : AccuracyRequest) (stage : Source.Result policy schedule extraDepth receipt.index request) :
    (integralBound (frontierFor retained receipt request stage).cells).Contains receipt.model.sample.re := by
  have inside := StageComparison.retainedFrontier_contains (requestFor retained receipt request) stage
  rw [stage_model retained receipt request stage] at inside
  exact inside

/-- A newly selected left stage with the actual saved right frontier and common readings. -/
@[expose] def afterStage {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right)
    (receipt : Model.Receipt retained) (request : AccuracyRequest)
    (stage : Source.Result policy schedule extraDepth receipt.index request)
    (common : Comparison.Observation.Certified (frontierFor retained receipt request stage) saved.rightFrontier) :
    Saved retained right :=
  let left := frontierFor retained receipt request stage
  { receipt := receipt
    leftRequest := request
    leftAnchor := stage
    leftModel := stage_model retained receipt request stage
    left := left
    leftInside := frontierFor_inside retained receipt request stage
    leftBank := left.cells.map (fun cell => cell.item) ++ common.val.readings.map CommonReading.leftPoint
    rightAnchor := saved.rightAnchor
    rightModel := saved.rightModel
    rightFrontier := saved.rightFrontier
    rightInside := saved.rightInside
    rightBank := saved.rightBank ++ common.val.readings.map CommonReading.rightPoint
    common := common }

/-- A newly selected left stage's actual frontier meets its original request. -/
theorem afterStage_accurate {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right)
    (receipt : Model.Receipt retained) (request : AccuracyRequest)
    (stage : Source.Result policy schedule extraDepth receipt.index request)
    (common : Comparison.Observation.Certified (frontierFor retained receipt request stage) saved.rightFrontier) :
    (integralBound (saved.afterStage receipt request stage common).left.cells).width < request.tolerance := by
  change (integralBound (frontierFor retained receipt request stage).cells).width < request.tolerance
  unfold frontierFor StageComparison.retainedFrontier
  rw [transport_width]
  have accurate := stage.sourceResult.accurate
  rw [stage.request_eq] at accurate
  exact accurate

/-- Transporting a value to an equal owner and back preserves that same value. -/
private theorem transport_cancel {A : Type} (P : A → Type) {first second : A}
    (same : first = second) (value : P second) : same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

/-- Any frontier of the saved receipt's source admits its original model sample. -/
theorem leftInside_any {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right)
    (frontier : SourceFrontier (Horner.Real.finiteSource saved.receipt.selection.depth)) :
    (integralBound frontier.cells).Contains saved.receipt.model.sample.re := by
  let same := StageComparison.Request.source_eq saved.request
  have inside := saved.leftAnchor.sample_contains (same.symm ▸ frontier)
  rw [saved.leftModel] at inside
  have transported := StageComparison.transport_contains same (same.symm ▸ frontier)
    saved.receipt.model.sample.re inside
  rw [transport_cancel (fun source => SourceFrontier source) same frontier] at transported
  exact transported

/-- Keep the old bank and all new exact observations retained by a source continuation. -/
@[expose] def continuationBank {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right)
    (step : SourceFrontier.Producer.Continuation
      (SourceFrontier.Continuous.producer (Horner.Real.finiteModulus saved.receipt.selection.depth)) saved.left) :
    List (SourcePoint (Horner.Real.finiteSource saved.receipt.selection.depth)) :=
  match step with
  | .reused _ _ => saved.leftBank
  | .refined _ _ fresh _ common _ =>
      saved.leftBank ++ fresh.frontier.cells.map (fun cell => cell.item) ++
        common.readings.map CommonReading.leftPoint

/-- Retain the actual refined left frontier and its returned common comparison with the unchanged right owner. -/
@[expose] def afterContinuation {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
    {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
    {right : StageComparison.Request rightPolicy rightSchedule rightExtra} (saved : Saved retained right)
    (step : SourceFrontier.Producer.Continuation
      (SourceFrontier.Continuous.producer (Horner.Real.finiteModulus saved.receipt.selection.depth)) saved.left)
    (common : Comparison.Observation.Certified step.frontier saved.rightFrontier) : Saved retained right :=
  { saved with
    left := step.frontier
    leftInside := saved.leftInside_any step.frontier
    leftBank := saved.continuationBank step ++ common.val.readings.map CommonReading.leftPoint
    rightBank := saved.rightBank ++ common.val.readings.map CommonReading.rightPoint
    common := common }


end Saved

end Purelib.Integration.Exponential.Program.Source.Observation.Runner

end
