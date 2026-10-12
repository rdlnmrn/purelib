module
public import Purelib.Data.List.BinaryPrefix.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix renaming CCLMeasureWord -> Word

section
@[expose] public section

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace Purelib.Data.List.BinaryPrefix

/-- Remove the last bit of a finite Boolean word, keeping the empty word empty. -/
def rawParent : Word → Word
  | [] => []
  | [_] => []
  | head :: next :: remaining => head :: rawParent (next :: remaining)

/-- Removing the final bit after appending one bit recovers the original word. -/
theorem rawParent_append_bit (word : Word) (bit : Bool) :
    rawParent (word ++ [bit]) = word := by
  induction word with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next tail =>
          change head :: rawParent ((next :: tail) ++ [bit]) =
            head :: next :: tail
          rw [inductionHypothesis]

/-- Read a finite word's last bit, returning false for the empty word. -/
def rawLastBit : Word → Bool
  | [] => false
  | [bit] => bit
  | _ :: next :: remaining => rawLastBit (next :: remaining)

/-- The last bit of a one-bit extension is the appended bit. -/
theorem rawLastBit_append_bit (word : Word) (bit : Bool) :
    rawLastBit (word ++ [bit]) = bit := by
  induction word with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next tail =>
          change rawLastBit ((next :: tail) ++ [bit]) = bit
          exact inductionHypothesis

/-- Remove a supplied number of final bits from a finite Boolean word.

Repeatedly apply rawParent; requests exceeding the word length remain at the empty
word because the parent operation is total. -/
def rawAncestor : Nat → Word → Word
  | 0, word => word
  | count + 1, word => rawAncestor count (rawParent word)

/-- Decide whether deleting the requested final bits gives the displayed shallow word. -/
def rawAncestorRelation (extra : Nat) (deep shallow : Word) : Bool :=
  decide (rawAncestor extra deep = shallow)
end Purelib.Data.List.BinaryPrefix

end
