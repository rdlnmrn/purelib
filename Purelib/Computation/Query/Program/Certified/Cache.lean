module

public import Purelib.Computation.Query.Program.Certified

/-! Indexed receipt execution with an original-owner bank. -/

public section

namespace Purelib.Computation.Query.Program.Certified.Cache

variable {Model Receipt Value : Type}

set_option genInjectivity false in
/-- A missing or wrong-index reply with the actual saved bank at the failed request. -/
inductive Failure (source : Source Model Receipt) where
  /-- The requested model operation received no receipt. -/ | operation (requested : Nat) (bank : List Receipt)
  /-- The actual returned receipt reported a different original index. -/ | index
      (requested : Nat) (receipt : Receipt) (bank : List Receipt) (different : source.index receipt ≠ requested)

set_option genInjectivity false in
/-- The complete original receipt execution and the actual updated receipt bank. -/
structure Completed (source : Source Model Receipt) (initial : List Receipt) (original : Program Nat Model Value) where
  /-- Every original model occurrence with its actual reused or newly returned receipt. -/ execution :
    Execution source original
  /-- The actual retained bank after this request. -/ bank : List Receipt
  /-- The caller's exact original bank remains the tail of the returned bank. -/ retained :
    ∃ added, bank = added ++ initial
  /-- Every original receipt occurrence is retained in the returned bank. -/ contains :
    ∀ exchange ∈ execution.val.trace, exchange.reply ∈ bank

/-- Find the first retained actual receipt for the original stage index. -/
@[expose] def find (source : Source Model Receipt) (index : Nat) :
    (bank : List Receipt) → Option {receipt : Receipt // source.index receipt = index ∧ receipt ∈ bank}
  | [] => none
  | receipt :: rest =>
      if same : source.index receipt = index then some ⟨receipt, same, List.Mem.head rest⟩
      else match find source index rest with
        | none => none
        | some found => some ⟨found.val, found.property.1, List.Mem.tail receipt found.property.2⟩

/-- Every original input receipt remains in the actual returned bank. -/
theorem Completed.retains {source : Source Model Receipt} {initial : List Receipt}
    {original : Program Nat Model Value} (result : Completed source initial original) {receipt : Receipt}
    (member : receipt ∈ initial) : receipt ∈ result.bank := by
  obtain ⟨added, same⟩ := result.retained
  rw [same]
  exact List.mem_append_right added member

/-- Prepend one reused original occurrence without changing the retained bank. -/
@[expose] def prependHit (source : Source Model Receipt) (initial : List Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (receipt : Receipt) (same : source.index receipt = index)
    (member : receipt ∈ initial) (after : Completed source initial (next (source.model receipt))) :
    Completed source initial (.request index next) := by
  refine ⟨prepend source index next receipt same after.execution, after.bank, after.retained, ?_⟩
  intro exchange present
  cases present with
  | head => exact after.retains member
  | tail _ present => exact after.contains exchange present

/-- Prepend one fresh original occurrence and retain the original caller bank as a tail. -/
@[expose] def prependFresh (source : Source Model Receipt) (initial : List Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (receipt : Receipt) (same : source.index receipt = index)
    (after : Completed source (receipt :: initial) (next (source.model receipt))) :
    Completed source initial (.request index next) := by
  refine ⟨prepend source index next receipt same after.execution, after.bank, ?_, ?_⟩
  · obtain ⟨added, retained⟩ := after.retained
    refine ⟨added ++ [receipt], ?_⟩
    rw [retained, List.append_assoc]
    rfl
  · intro exchange present
    cases present with
    | head => exact after.retains (List.Mem.head initial)
    | tail _ present => exact after.contains exchange present

/-- Reuse actual indexed receipts and display only original model queries missing from the bank.

Every reused or newly returned receipt still appears in the complete
certified original occurrence trace. A wrong operation or index retains the
actual bank; a wrong-index failure also retains the rejected receipt. -/
@[expose] def computation (source : Source Model Receipt) :
    (bank : List Receipt) → (original : Program Nat Model Value) →
      Program Nat (Option Receipt) (Except (Failure source) (Completed source bank original))
  | bank, .pure value => .pure (.ok ⟨⟨⟨value, []⟩, rfl, by intro exchange member; cases member⟩,
      bank, ⟨[], rfl⟩, by intro exchange member; cases member⟩)
  | bank, .request index next =>
      match find source index bank with
      | some receipt =>
          (computation source bank (next (source.model receipt.val))).map fun after =>
            after.map (prependHit source bank index next receipt.val receipt.property.1 receipt.property.2)
      | none => .request index fun reply =>
          match reply with
          | none => .pure (.error (.operation index bank))
          | some receipt =>
              if same : source.index receipt = index then
                (computation source (receipt :: bank) (next (source.model receipt))).map fun after =>
                  after.map (prependFresh source bank index next receipt same)
              else .pure (.error (.index index receipt bank same))

/-- A cached receipt selects its original continuation without a displayed source request. -/
theorem computation_hit (source : Source Model Receipt) (bank : List Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (receipt : {value : Receipt // source.index value = index ∧ value ∈ bank})
    (found : find source index bank = some receipt) :
    computation source bank (.request index next) =
      (computation source bank (next (source.model receipt.val))).map
        (fun after => after.map (prependHit source bank index next receipt.val
          receipt.property.1 receipt.property.2)) := by
  conv_lhs => rw [computation]
  rw [found]

/-- A missing cached index makes one displayed model request. -/
theorem computation_miss (source : Source Model Receipt) (bank : List Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (missing : find source index bank = none) :
    computation source bank (.request index next) =
      (.request index fun reply => match reply with
      | none => .pure (.error (.operation index bank))
      | some receipt =>
          if same : source.index receipt = index then
            (computation source (receipt :: bank) (next (source.model receipt))).map fun after =>
              after.map (prependFresh source bank index next receipt same)
          else .pure (.error (.index index receipt bank same))) := by
  conv_lhs => rw [computation]
  rw [missing]

/-- A matching receipt at the head of the bank is reused exactly. -/
theorem find_head (source : Source Model Receipt) (index : Nat) (receipt : Receipt)
    (bank : List Receipt) (same : source.index receipt = index) :
    find source index (receipt :: bank) = some ⟨receipt, same, List.Mem.head bank⟩ := by
  unfold find
  rw [dif_pos same]

/-- A bank containing a receipt for this index has an actual successful lookup. -/
theorem find_of_member (source : Source Model Receipt) (index : Nat) (bank : List Receipt)
    (receipt : Receipt) (member : receipt ∈ bank) (same : source.index receipt = index) :
    ∃ found, find source index bank = some found := by
  induction bank with
  | nil => cases member
  | cons head tail ih =>
      by_cases headSame : source.index head = index
      · exact ⟨⟨head, headSame, List.Mem.head tail⟩, find_head source index head tail headSame⟩
      · have inTail : receipt ∈ tail := by
          cases member with
          | head => exact False.elim (headSame same)
          | tail _ inTail => exact inTail
        obtain ⟨found, foundEq⟩ := ih inTail
        refine ⟨⟨found.val, found.property.1, List.Mem.tail head found.property.2⟩, ?_⟩
        change ((if headSame : source.index head = index then
          some ⟨head, headSame, List.Mem.head tail⟩
        else match find source index tail with
          | none => none
          | some found => some ⟨found.val, found.property.1, List.Mem.tail head found.property.2⟩) :
            Option {receipt : Receipt // source.index receipt = index ∧ receipt ∈ head :: tail}) = _
        rw [dif_neg headSame, foundEq]

/-- A supplied or just-returned head receipt prevents another query for the same index.

Fresh replies are inserted at the head, so this is also the no-call law for
the next repeated occurrence in the same original program. -/
theorem computation_head (source : Source Model Receipt) (bank : List Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (receipt : Receipt) (same : source.index receipt = index) :
    computation source (receipt :: bank) (.request index next) =
      (computation source (receipt :: bank) (next (source.model receipt))).map
        (fun after => after.map (prependHit source (receipt :: bank) index next receipt same
          (List.Mem.head bank))) :=
  computation_hit source (receipt :: bank) index next ⟨receipt, same, List.Mem.head bank⟩
    (find_head source index receipt bank same)

/-- Original indexed replies return a certified original model execution and updated bank. -/
theorem computation_original (source : Source Model Receipt) (answer : Nat → Receipt)
    (answer_index : ∀ index, source.index (answer index) = index) :
    ∀ (original : Program Nat Model Value) (bank : List Receipt),
      ∃ result : Completed source bank original,
        ((computation source bank original).protocol.run (fun index => some (answer index))).value = .ok result
  | .pure _, bank =>
      ⟨⟨⟨_, rfl, by intro exchange member; cases member⟩, bank, ⟨[], rfl⟩,
        by intro exchange member; cases member⟩, rfl⟩
  | .request index next, bank => by
      cases found : find source index bank with
      | some receipt =>
        obtain ⟨after, returned⟩ := computation_original source answer answer_index
          (next (source.model receipt.val)) bank
        rw [computation_hit source bank index next receipt found,
          Program.map_execution, Protocol.map_run_value, returned]
        exact ⟨prependHit source bank index next receipt.val receipt.property.1 receipt.property.2 after, rfl⟩
      | none =>
        obtain ⟨after, returned⟩ := computation_original source answer answer_index
          (next (source.model (answer index))) (answer index :: bank)
        rw [computation_miss source bank index next found]
        change ∃ result, ((if same : source.index (answer index) = index then
          (computation source (answer index :: bank) (next (source.model (answer index)))).map fun after =>
            after.map (prependFresh source bank index next (answer index) same)
          else Program.pure (.error (.index index (answer index) bank same))).protocol.run
            (fun index => some (answer index))).value = .ok result
        rw [dif_pos (answer_index index), Program.map_execution, Protocol.map_run_value, returned]
        exact ⟨prependFresh source bank index next (answer index) (answer_index index) after, rfl⟩

/-- Replay preserves the complete certified original execution or the actual typed failed attempt. -/
theorem computation_replay (source : Source Model Receipt) (bank : List Receipt)
    (original : Program Nat Model Value) (oracle : Nat → Option Receipt) :
    (computation source bank original).protocol.replayExact
      ((computation source bank original).protocol.run oracle).trace =
        .ok ((computation source bank original).protocol.run oracle).value :=
  (computation source bank original).protocol.replayExact_run oracle

/-- Replies outside the actual cache-miss trace preserve the complete execution. -/
theorem payload_erasure (source : Source Model Receipt) (bank : List Receipt)
    (original : Program Nat Model Value) (oracle : Nat → Option Receipt) {Payload : Type} (payload : Payload)
    (outside : Payload → Nat → Option Receipt) :
    (computation source bank original).protocol.run (Boundary.Trace.overlay
      ((computation source bank original).protocol.run oracle).trace (outside payload)) =
        (computation source bank original).protocol.run oracle :=
  (computation source bank original).protocol.annotation_erasure oracle payload outside

end Purelib.Computation.Query.Program.Certified.Cache

end
