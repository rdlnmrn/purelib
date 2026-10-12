module

import Init.Data.List.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Replicate

/-!
# Observations of the original finite list reversal

The reversal accumulator retains the supplied suffix and original entry order.
Structural certificates relate its original last-entry and prefix observations
to the complete reversed list, without replacing the reversal algorithm.
-/

namespace Purelib.Data.List.Reverse

open Purelib.Data.List

universe u v

/-- The original reversal accumulator preserves an appended retained suffix.

Each original head is transferred to the unchanged accumulator before the
remaining spine is scanned. The supplied final suffix remains in its original order. -/
private theorem reverseAux_append {Alpha : Type u} :
    ∀ (values before after : List Alpha),
      List.reverseAux values (before ++ after) = List.reverseAux values before ++ after
  | [], _, _ => rfl
  | head :: tail, before, after => reverseAux_append tail (head :: before) after

/-- Reversing a retained head places it after the reversed original tail.

The original reversal accumulator receives that displayed head as its singleton
suffix. Its appended-suffix identity preserves the original list constructor. -/
public theorem reverse_cons {Alpha : Type u} (head : Alpha) (tail : List Alpha) :
    (head :: tail).reverse = tail.reverse ++ [head] :=
  reverseAux_append tail [] [head]

/-- Reversing concatenation first reverses the retained right list, then the left.

Structural recursion transfers the original left heads to their final reversed
positions. Concatenation associativity preserves both original list orders. -/
public theorem reverse_append {Alpha : Type u} : ∀ left right : List Alpha,
    (left ++ right).reverse = right.reverse ++ left.reverse
  | [], right => (Append.append_nil right.reverse).symm
  | head :: tail, right => by
      rewrite [List.cons_append, reverse_cons, reverse_append tail right, reverse_cons,
        Append.append_assoc]
      exact Eq.refl _

/-- Reversing a replicated list retains its original repeated entries.

Every entry is the same supplied value. Structural recursion moves the head
to the unchanged repeated suffix, preserving the exact original count. -/
public theorem reverse_replicate {Alpha : Type u} (count : Nat) (value : Alpha) :
    (List.replicate count value).reverse = List.replicate count value := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (value :: List.replicate count value).reverse = value :: List.replicate count value
      rw [reverse_cons, ih]
      change List.replicate count value ++ [value] = List.replicate (count + 1) value
      exact (Replicate.replicate_add count 1 value).symm

/-- Reversing a retained finite list twice recovers its original entries.

Each original head returns to its original front position after the two
reversal scans. The unchanged tail follows by structural recursion. -/
public theorem reverse_reverse {Alpha : Type u} : ∀ values : List Alpha,
    values.reverse.reverse = values
  | [] => rfl
  | head :: tail => by
      rewrite [reverse_cons, reverse_append, reverse_reverse tail]
      exact Eq.refl _

/-- Reversing a finite list retains its original length.

Every original head becomes one final reversed entry. The original reversal
and append-length certificates count those same retained list positions. -/
public theorem length_reverse {Alpha : Type u} : ∀ values : List Alpha,
    values.reverse.length = values.length
  | [] => rfl
  | head :: tail => by
      rewrite [reverse_cons, Append.length_append, length_reverse tail]
      exact Eq.refl _

/-- Mapping commutes with the original finite reversal.

Every retained source entry contributes the same mapped value at its reversed
position. The two scans preserve the original tail and singleton entry order. -/
public theorem map_reverse {Alpha : Type u} {Beta : Type v} (mapper : Alpha → Beta) :
    ∀ values : List Alpha, values.reverse.map mapper = (values.map mapper).reverse
  | [] => rfl
  | head :: tail => by
      rewrite [reverse_cons, Map.map_append, List.map_singleton, List.map_cons,
        reverse_cons, map_reverse mapper tail]
      exact Eq.refl _

/-- A displayed last entry heads the original reversed list before its reversed prefix.

The retained `getLast?` equation identifies the actual final occurrence. The
original `dropLast` operation retains exactly its original preceding entries. -/
public theorem reverse_eq_getLast_cons_dropLast {Alpha : Type u} {last : Alpha} :
    ∀ values : List Alpha, values.getLast? = some last →
      values.reverse = last :: values.dropLast.reverse
  | [], impossible => by cases impossible
  | head :: tail, retained => by
      cases tail with
      | nil =>
          have equal : head = last := Option.some.inj retained
          cases equal
          rfl
      | cons next rest =>
          have tailRetained : (next :: rest).getLast? = some last := retained
          rewrite [reverse_cons,
            reverse_eq_getLast_cons_dropLast (next :: rest) tailRetained]
          change (last :: (next :: rest).dropLast.reverse) ++ [head] =
            last :: (head :: (next :: rest).dropLast).reverse
          rewrite [reverse_cons]
          exact Eq.refl _

/-- A retained last entry accounts for one slot beyond the original dropped prefix.

The original `getLast?` equation excludes the empty list. Each preceding head
increments both retained prefix and complete list counts in the same way. -/
public theorem length_dropLast_of_getLast {Alpha : Type u} {last : Alpha} :
    ∀ values : List Alpha, values.getLast? = some last →
      values.dropLast.length + 1 = values.length
  | [], impossible => by cases impossible
  | head :: tail, retained => by
      cases tail with
      | nil => rfl
      | cons next rest =>
          exact congrArg Nat.succ (length_dropLast_of_getLast (next :: rest) retained)

/-- Original reversal retains exactly the same finite list occurrences.

The original reverse accumulator places each head after its reversed tail.
Membership follows those retained constructors and concatenation occurrences
in both directions, without converting a logical equivalence into equality. -/
public theorem mem_reverse {Alpha : Type u} {target : Alpha} :
    ∀ values : List Alpha, target ∈ values.reverse ↔ target ∈ values
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · intro impossible
        nomatch impossible
  | head :: tail => by
      constructor
      · intro member
        rewrite [reverse_cons] at member
        cases Membership.mem_append.mp member with
        | inl inTail => exact List.Mem.tail head ((mem_reverse tail).mp inTail)
        | inr inHead =>
            have equal : target = head := Membership.mem_singleton.mp inHead
            cases equal
            exact List.Mem.head tail
      · intro member
        rewrite [reverse_cons]
        cases member with
        | head => exact Membership.mem_append.mpr (Or.inr (List.Mem.head []))
        | tail _ inTail =>
            exact Membership.mem_append.mpr (Or.inl ((mem_reverse tail).mpr inTail))

end Purelib.Data.List.Reverse
