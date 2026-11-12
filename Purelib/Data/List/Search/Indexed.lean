module

public import Purelib.Data.List.Search

/-! # Original retained values at bounded occurrence keys

A bounded original position is a key independently of the stored value.
The selected value is read from the original list, keeping repeated entries
and coordinate-equal observations at their separate positions.
-/

public section

namespace Purelib.Data.List.Search

universe u

variable {Item : Type u}

/-- One retained original list entry at its supplied bounded occurrence key.

The complete selected value and its original list identity are retained.
This is a positional lookup certificate, distinct from a value-predicate
first-match occurrence. It contains no copied identifier or new producer.
-/
@[expose] def At (entries : List Item) (key : Fin entries.length) :=
  {entry : Item // entry = entries[key.val]'key.isLt}

/-- Read the same complete original value at an actual bounded occurrence. -/
def select (entries : List Item) (key : Fin entries.length) : At entries key :=
  ⟨entries[key.val]'key.isLt, rfl⟩

namespace At

variable {entries : List Item} {key : Fin entries.length}

/-- The positional lookup retains the identical original complete entry. -/
theorem entry_eq (selected : At entries key) : selected.val = entries[key.val]'key.isLt := selected.property

/-- No earlier bounded occurrence has the same original position key.

This distinguishes positions, not entry values. Earlier equal values remain
separate occurrences and are not rejected by a value or coordinate test.
-/
theorem earlier_ne (earlier : Fin entries.length) (before : earlier.val < key.val) : earlier ≠ key := by
  intro same
  exact (Nat.ne_of_lt before) (congrArg Fin.val same)

end At

/-- The original positional lookup returns exactly its original complete value and factory witness. -/
private theorem packaged_select_factory (entries : List Item) (key : Fin entries.length) :
    select entries key = ⟨entries[key.val]'key.isLt, rfl⟩ := by
  unfold select
  rfl

/-- The original positional lookup returns exactly its original complete value and factory witness. -/
theorem select_factory (entries : List Item) (key : Fin entries.length) :
    select entries key = ⟨entries[key.val]'key.isLt, rfl⟩ :=
  packaged_select_factory entries key

end Purelib.Data.List.Search

end
