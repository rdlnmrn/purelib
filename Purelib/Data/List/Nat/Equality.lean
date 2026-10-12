module

import Purelib.Data.Bool.Decide

/-!
# Boolean equality of natural-number lists

Decode the original elementwise Boolean decision into structural list equality.
The recursion retains the original natural-number decision dictionary.
-/

namespace Purelib.Data.List.Nat.Equality

open Purelib.Data

/-- Boolean equality of natural-number lists implies their structural equality.

The recursion separates head equality and tail equality directly from List.beq,
without invoking a generic lawful Boolean-equality instance for lists. -/
public theorem listNat_eq_of_beq : ∀ left right : List Nat,
    List.beq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, equality => Bool.noConfusion equality
  | _ :: _, [], equality => Bool.noConfusion equality
  | left :: leftTail, right :: rightTail, equality => by
      change ((left == right) && List.beq leftTail rightTail) = true at equality
      have parts : (left == right) = true ∧
          List.beq leftTail rightTail = true :=
        (Bool.Decide.and_true_iff _ _).mp equality
      have headEquality : (left == right) = true := parts.1
      have tailEquality : List.beq leftTail rightTail = true := parts.2
      rw [of_decide_eq_true headEquality,
        listNat_eq_of_beq leftTail rightTail tailEquality]

end Purelib.Data.List.Nat.Equality
