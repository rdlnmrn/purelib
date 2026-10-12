module

import Purelib.Data.List.Reverse

/-!
# Optional and defaulting finite list coordinates

A retained list and its natural coordinate determine an optional entry; a
supplied fallback also defines a defaulting readback. Concatenation, reversal and out-of-range certificates concern
those same
spines and indices, without introducing a decidable membership construction.
-/

namespace Purelib.Data.List

universe u v

set_option backward.match.sparseCases false in
/-- Read a retained finite list coordinate, using the supplied fallback beyond its length.

A zero index reads the current head, and a successor consumes the same original
tail. Empty lists return the original fallback for every index; no bound witness
or membership enumeration replaces the original list and natural coordinate. -/
@[expose] public def getD {Alpha : Type u} : List Alpha → Nat → Alpha → Alpha
  | [], _, fallback => fallback
  | head :: _, 0, _ => head
  | _ :: tail, index + 1, fallback => getD tail index fallback

/-- Reading concatenation at the left length reads the first original right entry.

The same fallback and natural coordinate are retained. Each original left head
consumes one successor index before the unchanged right list is reached. -/
private theorem getD_append_at_length {Alpha : Type u} (left right : List Alpha)
    (fallback : Alpha) :
    getD (left ++ right) left.length fallback = getD right 0 fallback := by
  induction left with
  | nil => rfl
  | cons head tail retained => exact retained

/-- The last coordinate of a reversed nonempty list contains its original head.

The original reversal puts that head after the reversed tail. Their retained
lengths identify the same last coordinate, with the supplied fallback unchanged. -/
public theorem reverse_getD_last {Alpha : Type u} (head : Alpha) (tail : List Alpha)
    (fallback : Alpha) : getD (head :: tail).reverse tail.length fallback = head := by
  rewrite [Reverse.reverse_cons, ← Reverse.length_reverse tail,
    getD_append_at_length]
  exact Eq.refl _

set_option backward.match.sparseCases false in
/-- A coordinate at or beyond the retained list length returns its supplied fallback.

Each successor index consumes the original head and weak bound together.
The empty list returns the same fallback, while a zero index cannot satisfy the
required bound for a nonempty list. -/
public theorem getD_eq_default_of_length_le {Alpha : Type u} :
    ∀ (values : List Alpha) (index : Nat) (fallback : Alpha),
      values.length ≤ index → getD values index fallback = fallback
  | [], _, _, _ => rfl
  | _ :: _, 0, _, impossible => by cases impossible
  | _ :: remaining, index + 1, fallback, bound =>
      getD_eq_default_of_length_le remaining index fallback
        (Nat.le_of_succ_le_succ bound)

set_option backward.match.sparseCases false in
/-- Read a retained finite list coordinate, returning no entry beyond its length.

A zero coordinate reads the current head and a successor consumes its original
tail. The empty list returns none at every natural coordinate, without constructing
an index-bound proof or deciding membership of an independently copied list. -/
@[expose] public def getElem? {Alpha : Type u} : List Alpha → Nat → Option Alpha
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => getElem? tail index

set_option backward.match.sparseCases false in
/-- A successful optional coordinate reads an actual occurrence of its original list.

Structural recursion follows the retained coordinate and list spine together.
The zero case identifies the original head, and every successor retains the
same occurrence in the original tail. -/
public theorem mem_of_getElem? {Alpha : Type u} :
    ∀ (values : List Alpha) (index : Nat) (entry : Alpha),
      getElem? values index = some entry → entry ∈ values
  | [], _, _, impossible => by cases impossible
  | head :: tail, 0, entry, same => by
      have retained : head = entry := Option.some.inj same
      cases retained
      exact List.Mem.head tail
  | head :: tail, index + 1, entry, same =>
      List.Mem.tail head (mem_of_getElem? tail index entry same)

/-- Reading a mapped finite list maps the retained optional coordinate.

The same natural index consumes each original head and tail. Out-of-range
coordinates remain absent, while a present entry applies the supplied function once. -/
public theorem getElem?_map {Alpha : Type u} {Beta : Type v}
    (function : Alpha → Beta) (values : List Alpha) (index : Nat) :
    getElem? (values.map function) index = (getElem? values index).map function := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail retained =>
    cases index with
    | zero => rfl
    | succ index => exact retained index

/-- A bounded optional coordinate contains the exact original indexed entry.

The supplied strict length bound is retained explicitly. Structural recursion
consumes its successor bound along with the original list tail. -/
public theorem getElem?_eq_getElem {Alpha : Type u} (values : List Alpha)
    (index : Nat) (bound : index < values.length) :
    getElem? values index = some (values[index]'bound) := by
  induction values generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero index bound)
  | cons head tail retained =>
    cases index with
    | zero => rfl
    | succ index => exact retained index (Nat.lt_of_succ_lt_succ bound)

/-- Transporting a bounded index along a list equality preserves its original entry.

The equality changes only the displayed list and its length certificate. The same
natural coordinate reads the original retained value after that transport. -/
public theorem at_cast {Alpha : Type} {first last : List Alpha} (equal : first = last) (index : Fin first.length) :
    last[(Fin.cast (congrArg List.length equal) index).val]'
      (Fin.cast (congrArg List.length equal) index).isLt = first[index.val]'index.isLt := by
  cases equal
  rfl

end Purelib.Data.List
