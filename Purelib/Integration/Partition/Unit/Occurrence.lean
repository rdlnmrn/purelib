module

public import Purelib.Data.List.Search
public import Purelib.Integration.Partition.Unit.Presentation

namespace Purelib.Integration.Partition.Unit.Occurrence

open Purelib.Data
open Purelib.Data.Rat
open Presentation

/-- The original first noninterior occurrence in a particular list of cuts. -/
public abbrev Selected (cuts : Code) := List.Search.Occurrence (fun cut => ¬ Interior cut) cuts

/-- A proposed position names the first noninterior occurrence in the original list. -/
public def Valid (cuts : Code) (position : Nat) : Prop :=
  ∃ selected : Selected cuts, selected.index.val = position

/-- Occurrences at the same original bounded position have the same retained entry and proof fields. -/
public theorem eq_of_index_eq {cuts : Code} (left right : Selected cuts)
    (equal : left.index = right.index) : left = right := by
  rcases left with ⟨leftIndex, leftEntry⟩
  rcases right with ⟨rightIndex, rightEntry⟩
  cases equal
  congr 1
  apply Subtype.ext
  exact leftEntry.property.1.trans rightEntry.property.1.symm

/-- A fixed list has at most one first noninterior occurrence. -/
public theorem subsingleton {cuts : Code} (left right : Selected cuts) : left = right := by
  apply eq_of_index_eq
  apply Fin.ext
  cases Nat.lt_trichotomy left.index.val right.index.val with
  | inl before =>
      exact False.elim ((right.earlier left.index before) (left.entry_eq ▸ left.accepted))
  | inr rest =>
      cases rest with
      | inl equal => exact equal
      | inr before =>
          exact False.elim ((left.earlier right.index before) (right.entry_eq ▸ right.accepted))

/-- The original bounded position quotes an occurrence as a valid proposal. -/
public theorem valid_index {cuts : Code} (selected : Selected cuts) :
    Valid cuts selected.index.val := ⟨selected, rfl⟩

/-- The bounded position determines the complete original occurrence. -/
public theorem eq_iff_index_eq {cuts : Code} (left right : Selected cuts) :
    left = right ↔ left.index = right.index := by
  constructor
  · intro equal
    exact congrArg List.Search.Occurrence.index equal
  · exact eq_of_index_eq left right

/-- An occurrence's original bounded index and retained entry determine its identity.

The list and predicate remain fixed indices. Certificates of entry equality,
acceptance and all earlier rejections are proof-irrelevant. -/
public theorem eq_iff_index_entry_eq {cuts : Code} (left right : Selected cuts) :
    left = right ↔ left.index = right.index ∧ left.entry = right.entry := by
  constructor
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩
  · intro equal
    exact eq_of_index_eq left right equal.1

set_option genInjectivity false in
/-- A proposed position is accepted or rejected with its concrete reason. -/
public inductive Check (cuts : Code) (position : Nat) where
  /-- The proposed position is outside the original list. -/
  | outOfRange (failed : ¬ position < cuts.length)
  /-- The finite scan found no noninterior entry. -/
  | noOccurrence (invalid : ¬ Valid cuts position)
  /-- The scan found a different first noninterior position. -/
  | wrongPosition (selected : Selected cuts) (different : selected.index.val ≠ position)
  /-- The scan retained the proposed occurrence and its original entry. -/
  | accepted (selected : Selected cuts) (atPosition : selected.index.val = position)

/-- Validate a proposed position using the same finite scan as normalized-cut recognition. -/
public def check (cuts : Code) (position : Nat) : Check cuts position :=
  if bounded : position < cuts.length then
    match result : List.Search.firstOccurrence (fun cut => ¬ Interior cut)
        (fun cut => inferInstance) cuts with
    | some selected =>
        if atPosition : selected.index.val = position then
          .accepted selected atPosition
        else
          .wrongPosition selected atPosition
    | none => .noOccurrence (by
        rintro ⟨selected, _⟩
        have found := List.Search.firstAccepted (fun cut => ¬ Interior cut)
          (fun cut => inferInstance) cuts ⟨selected.entry, selected.member, selected.accepted⟩
        have impossible : none = some found.val := result.symm.trans found.property
        cases impossible)
  else .outOfRange bounded

/-- Decide proposed-position validity from the typed finite check. -/
public def recognize (cuts : Code) (position : Nat) : Decidable (Valid cuts position) :=
  match check cuts position with
  | .outOfRange failed => .isFalse (by
      rintro ⟨selected, equal⟩
      exact failed (equal ▸ selected.index.isLt))
  | .noOccurrence invalid => .isFalse invalid
  | .wrongPosition selected different => .isFalse (by
      rintro ⟨other, equal⟩
      exact different ((congrArg (fun x : Selected cuts => x.index.val) (subsingleton selected other)).trans equal))
  | .accepted selected atPosition => .isTrue ⟨selected, atPosition⟩

/-- A proposed position and entry describe the same original first noninterior cut. -/
public def EntryValid (cuts : Code) (position : Nat) (entry : Fraction.Rational) : Prop :=
  ∃ selected : Selected cuts, selected.index.val = position ∧ selected.entry = entry

set_option genInjectivity false in
/-- A proposed occurrence pair is accepted or rejected with its original position-check result. -/
public inductive EntryCheck (cuts : Code) (position : Nat) (entry : Fraction.Rational) where
  /-- The original position checker rejects the proposed position. -/
  | invalidPosition (reason : Check cuts position) (invalid : ¬ Valid cuts position)
  /-- The position is first, but its retained entry differs from the proposed entry. -/
  | wrongEntry (selected : Selected cuts) (atPosition : selected.index.val = position)
      (different : selected.entry ≠ entry)
  /-- The original first occurrence retains both proposed fields. -/
  | accepted (selected : Selected cuts) (atPosition : selected.index.val = position)
      (sameEntry : selected.entry = entry)

/-- Check the original bounded position and its retained entry with one occurrence scan.

An accepted `Selected` carries rejection of every earlier original cut. The
entry is compared with that exact selected value rather than reconstructed. -/
public def checkEntry (cuts : Code) (position : Nat) (entry : Fraction.Rational) :
    EntryCheck cuts position entry :=
  match check cuts position with
  | .outOfRange failed => .invalidPosition (.outOfRange failed) (by
      rintro ⟨selected, equal⟩
      exact failed (equal ▸ selected.index.isLt))
  | .noOccurrence invalid => .invalidPosition (.noOccurrence invalid) invalid
  | .wrongPosition selected different => .invalidPosition (.wrongPosition selected different) (by
      rintro ⟨other, equal⟩
      exact different ((congrArg (fun x : Selected cuts => x.index.val) (subsingleton selected other)).trans equal))
  | .accepted selected atPosition =>
      if same : selected.entry = entry then .accepted selected atPosition same
      else .wrongEntry selected atPosition same

/-- Derive the pair-validity decision from the detailed original occurrence check. -/
public def EntryCheck.decision {cuts : Code} {position : Nat} {entry : Fraction.Rational}
    (result : EntryCheck cuts position entry) : Decidable (EntryValid cuts position entry) :=
  match result with
  | .invalidPosition _ invalid => .isFalse (fun ⟨selected, atPosition, _⟩ => invalid ⟨selected, atPosition⟩)
  | .wrongEntry selected _ different => .isFalse (fun ⟨other, _, sameEntry⟩ =>
      different ((congrArg (fun x : Selected cuts => x.entry) (subsingleton selected other)).trans sameEntry))
  | .accepted selected atPosition sameEntry => .isTrue ⟨selected, atPosition, sameEntry⟩

/-- Decide a proposed position and entry by the same finite occurrence check. -/
public def recognizeEntry (cuts : Code) (position : Nat) (entry : Fraction.Rational) :
    Decidable (EntryValid cuts position entry) := (checkEntry cuts position entry).decision

end Purelib.Integration.Partition.Unit.Occurrence
