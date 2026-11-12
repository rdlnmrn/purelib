module

public import Purelib.Integration.Cell.Numerical.Common.Observation.Independent
public import Purelib.Integration.Cell.Numerical.Common.Cache

/-! Original common occurrences with two independent retained point banks. -/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Observation.Independent.Cache

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Integration.NumericalFrontier

variable {leftSource rightSource : Fraction.Rational → BoundProcess}
variable (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource)
variable (leftBank : List (NumericalPoint leftSource)) (rightBank : List (NumericalPoint rightSource))
variable (request : AccuracyRequest)

set_option genInjectivity false in
/-- A failed common request with every completed child and both retained original-owner banks. -/
structure Failure (Reason : Type) (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) where
  /-- The original common occurrence whose point request failed. -/ failed : Independent.Index left right
  /-- The first invalid original owner or operation. -/ reason : Reason
  /-- The actual completed common children before the failing occurrence. -/ completed :
    List (CommonReading left right request)
  /-- Actual completed or partially completed left observations, in original order. -/ leftAdded :
    List (NumericalPoint leftSource)
  /-- Actual completed right observations, in original order. -/ rightAdded : List (NumericalPoint rightSource)
  /-- The actual returned left point bank. -/ leftBank : List (NumericalPoint leftSource)
  /-- The actual returned right point bank. -/ rightBank : List (NumericalPoint rightSource)
  /-- The actual left additions precede the exact caller-supplied left bank. -/ left_retained :
    leftBank = leftAdded ++ savedLeft
  /-- The actual right additions precede the exact caller-supplied right bank. -/ right_retained :
    rightBank = rightAdded ++ savedRight

/-- Retain the original supplied banks at a first failed left-side operation. -/
@[expose] def Failure.initial (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) {Reason : Type} (failed : Independent.Index left right)
    (reason : Reason) : Failure left right request Reason savedLeft savedRight :=
  ⟨failed, reason, [], [], [], savedLeft, savedRight, rfl, rfl⟩

/-- Retain the actual left observation when the corresponding right operation fails. -/
@[expose] def Failure.afterLeft (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) {Reason : Type} (failed : Independent.Index left right)
    (reason : Reason) (point : NumericalPoint leftSource) : Failure left right request Reason savedLeft savedRight :=
  ⟨failed, reason, [], [point], [], point :: savedLeft, savedRight, rfl, rfl⟩

/-- The actual retained left and right points available to their own source requests. -/
abbrev leftAvailable := Common.Cache.available left leftBank

/-- The actual retained right points, in supplied-bank then frontier order. -/
abbrev rightAvailable := Common.Cache.available right rightBank

/-- The original cached left observation at one common occurrence. -/
@[expose] def leftPoint (index : Independent.Index left right) :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  NumericalPoint.atCached leftSource leftBank child child.start le_rfl valid.2.1.le request

/-- The original cached right observation at one common occurrence. -/
@[expose] def rightPoint (index : Independent.Index left right) :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  NumericalPoint.atCached rightSource rightBank child child.start le_rfl valid.2.1.le request

/-- A returned left point is certified against its actual original bank and occurrence. -/
abbrev LeftSelected (index : Independent.Index left right) :=
  {point : NumericalPoint leftSource // point = (leftPoint left right leftBank request index).val}

/-- A returned right point is certified against its actual original bank and occurrence. -/
abbrev RightSelected (index : Independent.Index left right) :=
  {point : NumericalPoint rightSource // point = (rightPoint left right rightBank request index).val}

/-- One returned original occurrence and its owner-specific cached point. -/
abbrev Reply := Sum (Σ index : Independent.Index left right, LeftSelected left right leftBank request index)
  (Σ index : Independent.Index left right, RightSelected left right rightBank request index)

/-- Decode a returned left point only for its original common occurrence. -/
@[expose] def decodeLeft (index : Independent.Index left right)
    (reply : Reply left right leftBank rightBank request) :
    Except (Independent.Failure left right) (LeftSelected left right leftBank request index) :=
  match reply with
  | .inr _ => .error (.owner (.inl index))
  | .inl ⟨reported, point⟩ =>
      if same : reported = index then .ok (same ▸ point) else .error (.index index reported same)

/-- Decode a returned right point only for its original common occurrence. -/
@[expose] def decodeRight (index : Independent.Index left right)
    (reply : Reply left right leftBank rightBank request) :
    Except (Independent.Failure left right) (RightSelected left right rightBank request index) :=
  match reply with
  | .inl _ => .error (.owner (.inr index))
  | .inr ⟨reported, point⟩ =>
      if same : reported = index then .ok (same ▸ point) else .error (.index index reported same)

/-- Observe one cached left point, asking its source only when its bank selection requires it. -/
@[expose] def leftRequest (index : Independent.Index left right) :
    Program (Independent.Query left right) (Reply left right leftBank rightBank request)
      (Except (Independent.Failure left right) (LeftSelected left right leftBank request index)) :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  Independent.pointWithDecision child child.start le_rfl valid.2.1.le request
    (NumericalPoint.selectBank leftSource leftBank child.start request)
    (leftPoint left right leftBank request index).val rfl (.inl index)
    (decodeLeft left right leftBank rightBank request index)

/-- Observe one cached right point, asking its own source only when its bank selection requires it. -/
@[expose] def rightRequest (index : Independent.Index left right) :
    Program (Independent.Query left right) (Reply left right leftBank rightBank request)
      (Except (Independent.Failure left right) (RightSelected left right rightBank request index)) :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  Independent.pointWithDecision child child.start le_rfl valid.2.1.le request
    (NumericalPoint.selectBank rightSource rightBank child.start request)
    (rightPoint left right rightBank request index).val rfl (.inr index)
    (decodeRight left right leftBank rightBank request index)

/-- An original reply retains the exact source owner, occurrence and bank-selected point. -/
@[expose] def originalReply : Independent.Query left right → Reply left right leftBank rightBank request
  | .inl index => .inl ⟨index, ⟨(leftPoint left right leftBank request index).val, rfl⟩⟩
  | .inr index => .inr ⟨index, ⟨(rightPoint left right rightBank request index).val, rfl⟩⟩

/-- The returned left and right points at one original common occurrence. -/
abbrev SelectedPair (index : Independent.Index left right) :=
  LeftSelected left right leftBank request index × RightSelected left right rightBank request index

/-- Request the original left and right bank-selected points in order.

A failed right request retains the actual left point already returned at the
same original occurrence and both supplied original-owner banks. -/
@[expose] def pair (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (index : Independent.Index left right) :
    Program (Independent.Query left right) (Reply left right leftBank rightBank request)
      (Except (Failure left right request (Independent.Failure left right) savedLeft savedRight)
        (SelectedPair left right leftBank rightBank request index)) :=
  (leftRequest left right leftBank rightBank request index).bind fun first => match first with
    | .error invalid => .pure (.error (Failure.initial left right request savedLeft savedRight index invalid))
    | .ok first => (rightRequest left right leftBank rightBank request index).map fun second =>
        match second with
        | .error invalid => .error (Failure.afterLeft left right request savedLeft savedRight index invalid first.val)
        | .ok second => .ok (first, second)

/-- The exact original cached pair at this occurrence. -/
@[expose] def targetPair (index : Independent.Index left right) :=
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  Common.Cache.cachedPair leftBank rightBank
    child child.start ⟨le_rfl, valid.2.1.le⟩ request

/-- Build the common child from the actual returned bank-selected points. -/
@[expose] def returnedChild (index : Independent.Index left right)
    (points : SelectedPair left right leftBank rightBank request index) : CommonReading left right request := by
  let child := (Independent.entry left right index).val.child
  let valid := Independent.entryValid left right index
  let leftObservation := leftPoint left right leftBank request index
  let rightObservation := rightPoint left right rightBank request index
  have leftEq := points.1.property
  have rightEq := points.2.property
  let actualLeft : NumericalPoint.Observation leftSource child child.start request :=
    ⟨points.1.val, leftEq.symm ▸ leftObservation.property⟩
  let actualRight : NumericalPoint.Observation rightSource child child.start request :=
    ⟨points.2.val, rightEq.symm ▸ rightObservation.property⟩
  exact readCommonFromPair left right request (Independent.entry left right index).val valid child.start
    ⟨le_rfl, valid.2.1.le⟩
    (Common.Cache.pairFromObservations child child.start ⟨le_rfl, valid.2.1.le⟩ request
      actualLeft actualRight)

/-- The original cached child at one retained common occurrence. -/
@[expose] def occurrenceChild (occurrence : Independent.Occurrence left right) : CommonReading left right request :=
  let child := occurrence.val.child
  let valid := Independent.occurrenceValid left right occurrence
  readCommonFromPair left right request occurrence.val valid child.start ⟨le_rfl, valid.2.1.le⟩
    (Common.Cache.cachedPair leftBank rightBank child child.start
      ⟨le_rfl, valid.2.1.le⟩ request)

/-- The original cached child at one indexed common occurrence. -/
@[expose] def originalChild (index : Independent.Index left right) : CommonReading left right request :=
  occurrenceChild left right leftBank rightBank request (Independent.entry left right index)

/-- Returned points assemble to the same original bank-selected common child. -/
theorem returnedChild_eq (index : Independent.Index left right)
    (points : SelectedPair left right leftBank rightBank request index) :
    returnedChild left right leftBank rightBank request index points =
      originalChild left right leftBank rightBank request index := by
  cases points with
  | mk first second =>
    cases first with
    | mk first firstEq =>
      cases second with
      | mk second secondEq =>
        cases firstEq
        cases secondEq
        rfl

/-- Retain one earlier completed child and its actual two selected observations on a later failure. -/
@[expose] def Failure.prepend (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) (index : Independent.Index left right)
    (points : SelectedPair left right leftBank rightBank request index)
    {Reason : Type} (failure : Failure left right request Reason savedLeft savedRight) :
    Failure left right request Reason savedLeft savedRight :=
  ⟨failure.failed, failure.reason,
    returnedChild left right leftBank rightBank request index points :: failure.completed,
    points.1.val :: failure.leftAdded, points.2.val :: failure.rightAdded,
    points.1.val :: failure.leftBank, points.2.val :: failure.rightBank,
    congrArg (List.cons points.1.val) failure.left_retained,
    congrArg (List.cons points.2.val) failure.right_retained⟩

/-- Observe ordered common occurrences through any original owner-specific point-pair program. -/
@[expose] def batchWith {Question Reply Reason : Type}
    (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (readPair : (index : Independent.Index left right) → Program Question Reply
      (Except (Failure left right request Reason savedLeft savedRight)
        (SelectedPair left right leftBank rightBank request index))) :=
  Program.certifiedBatch (originalChild left right leftBank rightBank request)
    (SelectedPair left right leftBank rightBank request) (returnedChild left right leftBank rightBank request)
    (returnedChild_eq left right leftBank rightBank request)
    (fun index points failure =>
      Failure.prepend left right leftBank rightBank request savedLeft savedRight index points failure) readPair

/-- Observe ordered common occurrences using the original bank-selected numerical-point replies. -/
@[expose] def batch (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource)) :=
  batchWith left right leftBank rightBank request savedLeft savedRight
    (pair left right leftBank rightBank request savedLeft savedRight)

/-- Original replies return the actual selected left bank point. -/
theorem leftRequest_original (index : Independent.Index left right) :
    ((leftRequest left right leftBank rightBank request index).protocol.run
      (originalReply left right leftBank rightBank request)).value =
        .ok ⟨(leftPoint left right leftBank request index).val, rfl⟩ := by
  unfold leftRequest
  apply Independent.pointWithDecision_original
  change decodeLeft left right leftBank rightBank request index
    (.inl ⟨index, ⟨(leftPoint left right leftBank request index).val, rfl⟩⟩) = _
  unfold decodeLeft
  dsimp only
  rw [dif_pos rfl]

/-- Original replies return the actual selected right bank point. -/
theorem rightRequest_original (index : Independent.Index left right) :
    ((rightRequest left right leftBank rightBank request index).protocol.run
      (originalReply left right leftBank rightBank request)).value =
        .ok ⟨(rightPoint left right rightBank request index).val, rfl⟩ := by
  unfold rightRequest
  apply Independent.pointWithDecision_original
  change decodeRight left right leftBank rightBank request index
    (.inr ⟨index, ⟨(rightPoint left right rightBank request index).val, rfl⟩⟩) = _
  unfold decodeRight
  dsimp only
  rw [dif_pos rfl]

/-- Original replies return the independently selected original bank points in order. -/
theorem pair_original (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (index : Independent.Index left right) :
    ((pair left right leftBank rightBank request savedLeft savedRight index).protocol.run
      (originalReply left right leftBank rightBank request)).value =
        .ok (⟨(leftPoint left right leftBank request index).val, rfl⟩,
          ⟨(rightPoint left right rightBank request index).val, rfl⟩) := by
  unfold pair
  rw [Program.bind_execution, Protocol.bind_run_value, leftRequest_original]
  rewrite [Program.map_execution, Protocol.map_run_value, rightRequest_original]
  rfl

/-- The original indexed cached children are the complete original common reading list. -/
theorem originalChildren :
    (Purelib.Data.List.indices (Independent.occurrences left right)).map
      (originalChild left right leftBank rightBank request) =
        (Common.Cache.commonReadings left right leftBank rightBank request).readings := by
  change (Purelib.Data.List.indices (Independent.occurrences left right)).map
    ((occurrenceChild left right leftBank rightBank request) ∘ (Independent.occurrences left right).get) = _
  rw [← Purelib.Data.List.Map.map_map, Purelib.Data.List.indices_get]
  rfl

/-- Assemble the original common refinement from its actual returned bank-selected children. -/
@[expose] def assemble (returned : Program.CertifiedBatch (originalChild left right leftBank rightBank request)
    (Purelib.Data.List.indices (Independent.occurrences left right))) : CommonReadings left right request := by
  have entries_eq : returned.val.map CommonReading.entry =
      (Unit.Common.commonRefinement left.partition right.partition).entries := by
    rw [returned.property, originalChildren left right leftBank rightBank request]
    exact (Common.Cache.commonReadings left right leftBank rightBank request).entries_eq
  exact ⟨Unit.Common.commonRefinement left.partition right.partition, returned.val, entries_eq⟩

/-- The returned children assemble to the original two-bank common reading collection. -/
theorem assemble_eq (returned : Program.CertifiedBatch (originalChild left right leftBank rightBank request)
    (Purelib.Data.List.indices (Independent.occurrences left right))) :
    assemble left right leftBank rightBank request returned =
      Common.Cache.commonReadings left right leftBank rightBank request := by
  refine CommonReadings.ext _ _ rfl ?_
  exact returned.property.trans (originalChildren left right leftBank rightBank request)

/-- Assemble common readings from a supplied owner-specific point-pair program.

Earlier completed children and both actual banks are retained if a later
point-pair request fails. -/
@[expose] def computationWithPair {Question Reply Reason : Type}
    (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (readPair : (index : Independent.Index left right) → Program Question Reply
      (Except (Failure left right request Reason savedLeft savedRight)
        (SelectedPair left right leftBank rightBank request index))) :
    Program Question Reply (Except (Failure left right request Reason savedLeft savedRight)
      (CommonReadings left right request)) :=
  (batchWith left right leftBank rightBank request savedLeft savedRight readPair
    (Purelib.Data.List.indices (Independent.occurrences left right))).map fun returned =>
      returned.map (assemble left right leftBank rightBank request)

/-- Observe common occurrences using two already retained effective point banks. -/
@[expose] def computationWith (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) :
    Program (Independent.Query left right) (Reply left right leftBank rightBank request)
      (Except (Failure left right request (Independent.Failure left right) savedLeft savedRight)
        (CommonReadings left right request)) :=
  computationWithPair left right leftBank rightBank request savedLeft savedRight
    (pair left right leftBank rightBank request savedLeft savedRight)

/-- The exact stopped original common batch, including its certified ordered prefix. -/
abbrev BatchStopped (savedLeft : List (NumericalPoint leftSource))
    (savedRight : List (NumericalPoint rightSource)) (Reason : Type) :=
  Program.CertifiedBatch.Stopped (originalChild left right leftBank rightBank request)
    (Purelib.Data.List.indices (Independent.occurrences left right))
    (Failure left right request Reason savedLeft savedRight)

/-- Observe the original common occurrences while retaining a certified prefix on failure. -/
@[expose] def batchWithProgress {Question Reply Reason : Type}
    (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (readPair : (index : Independent.Index left right) → Program Question Reply
      (Except (Failure left right request Reason savedLeft savedRight)
        (SelectedPair left right leftBank rightBank request index))) :=
  Program.certifiedBatchProgress (originalChild left right leftBank rightBank request)
    (SelectedPair left right leftBank rightBank request) (returnedChild left right leftBank rightBank request)
    (returnedChild_eq left right leftBank rightBank request)
    (fun index points failure =>
      Failure.prepend left right leftBank rightBank request savedLeft savedRight index points failure) readPair

/-- Assemble the original common refinement and retain any certified completed prefix on failure. -/
@[expose] def computationWithPairProgress {Question Reply Reason : Type}
    (savedLeft : List (NumericalPoint leftSource)) (savedRight : List (NumericalPoint rightSource))
    (readPair : (index : Independent.Index left right) → Program Question Reply
      (Except (Failure left right request Reason savedLeft savedRight)
        (SelectedPair left right leftBank rightBank request index))) :
    Program Question Reply (Except (BatchStopped left right leftBank rightBank request savedLeft savedRight Reason)
      (CommonReadings left right request)) :=
  (batchWithProgress left right leftBank rightBank request savedLeft savedRight readPair
    (Purelib.Data.List.indices (Independent.occurrences left right))).map fun returned =>
      returned.map (assemble left right leftBank rightBank request)

/-- Observe both actual owner banks through their original ordered common occurrences.

The supplied banks are extended with their own actual frontier points once;
the same two effective values are passed to every child request. -/
@[expose] def computation :
    let actualLeft := leftAvailable left leftBank
    let actualRight := rightAvailable right rightBank
    Program (Independent.Query left right) (Reply left right actualLeft actualRight request)
      (Except (Failure left right request (Independent.Failure left right) leftBank rightBank)
        (CommonReadings left right request)) :=
  let actualLeft := leftAvailable left leftBank
  let actualRight := rightAvailable right rightBank
  computationWith left right actualLeft actualRight request leftBank rightBank

/-- Original replies return the complete original two-bank common reading collection. -/
theorem computation_original :
    let actualLeft := leftAvailable left leftBank
    let actualRight := rightAvailable right rightBank
    ((computation left right leftBank rightBank request).protocol.run
      (originalReply left right actualLeft actualRight request)).value =
        .ok (Common.Cache.commonReadings left right actualLeft actualRight request) := by
  let actualLeft := leftAvailable left leftBank
  let actualRight := rightAvailable right rightBank
  change ((computation left right leftBank rightBank request).protocol.run
    (originalReply left right actualLeft actualRight request)).value = _
  unfold computation computationWith computationWithPair batchWith
  rw [Program.map_execution, Protocol.map_run_value,
    Program.certifiedBatch_original (originalChild left right actualLeft actualRight request)
      (SelectedPair left right actualLeft actualRight request) (returnedChild left right actualLeft actualRight request)
      (returnedChild_eq left right actualLeft actualRight request)
      (fun index points failure => Failure.prepend left right actualLeft actualRight request
        leftBank rightBank index points failure)
      (pair left right actualLeft actualRight request leftBank rightBank)
      (originalReply left right actualLeft actualRight request)
      (fun index => (⟨(leftPoint left right actualLeft request index).val, rfl⟩,
        ⟨(rightPoint left right actualRight request index).val, rfl⟩))
      (pair_original left right actualLeft actualRight request leftBank rightBank)]
  apply congrArg Except.ok
  exact assemble_eq left right actualLeft actualRight request _

/-- Exact replay preserves the actual ordered two-owner common result or first invalid reply. -/
theorem computation_replay (oracle : Independent.Query left right →
    Reply left right (leftAvailable left leftBank) (rightAvailable right rightBank) request) :
    (computation left right leftBank rightBank request).protocol.replayExact
      ((computation left right leftBank rightBank request).protocol.run oracle).trace =
        .ok ((computation left right leftBank rightBank request).protocol.run oracle).value :=
  (computation left right leftBank rightBank request).protocol.replayExact_run oracle

/-- Changing replies outside the actual bank-miss trace preserves the complete common execution. -/
theorem payload_erasure (oracle : Independent.Query left right →
    Reply left right (leftAvailable left leftBank) (rightAvailable right rightBank) request)
    {Payload : Type} (payload : Payload) (outside : Payload → Independent.Query left right →
      Reply left right (leftAvailable left leftBank) (rightAvailable right rightBank) request) :
    (computation left right leftBank rightBank request).protocol.run (Boundary.Trace.overlay
      ((computation left right leftBank rightBank request).protocol.run oracle).trace (outside payload)) =
        (computation left right leftBank rightBank request).protocol.run oracle :=
  (computation left right leftBank rightBank request).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.NumericalFrontier.Common.Observation.Independent.Cache

end
