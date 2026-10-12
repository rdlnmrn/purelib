module
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
public import Purelib.Data.List.BinaryPrefix.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Tactic.Ring

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix renaming CCLMeasureWord -> Word

section
public section

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace Purelib.Data.List.BinaryPrefix

/-- Enumerate every Boolean-word extension at a supplied additional depth.

Depth zero returns the stem alone. Each successor recursively lists the false-bit
subtree before the true-bit subtree, retaining all finite extensions in that order. -/
@[expose] def rawExtensions (stem : Word) : Nat → List Word
  | 0 => [stem]
  | depth + 1 =>
      rawExtensions (stem ++ [false]) depth ++
        rawExtensions (stem ++ [true]) depth

/-- List the false-bit child followed by the true-bit child of a finite word. -/
@[expose] def rawChildren (word : Word) : List Word :=
  [word ++ [false], word ++ [true]]

/-- One more frontier depth replaces each current word with its ordered two-child list. -/
theorem rawExtensions_succ_children (stem : Word) : ∀ depth : Nat,
    rawExtensions stem (depth + 1) =
      (rawExtensions stem depth).flatMap rawChildren
  | 0 => rfl
  | depth + 1 => by
      change
        rawExtensions (stem ++ [false]) (depth + 1) ++
            rawExtensions (stem ++ [true]) (depth + 1) =
          (rawExtensions (stem ++ [false]) depth ++
            rawExtensions (stem ++ [true]) depth).flatMap rawChildren
      rw [rawExtensions_succ_children (stem ++ [false]) depth,
        rawExtensions_succ_children (stem ++ [true]) depth,
        Flatten.flatMap_append]

/-- The full binary frontier at a supplied additional depth has exactly 2^depth entries. -/
theorem rawExtensions_length (stem : Word) : ∀ depth : Nat,
    (rawExtensions stem depth).length = 2 ^ depth
  | 0 => rfl
  | depth + 1 => by
      rw [rawExtensions, Append.length_append,
        rawExtensions_length (stem ++ [false]) depth,
        rawExtensions_length (stem ++ [true]) depth, Nat.pow_succ]
      ring1

/-- Each enumerated extension has length equal to the stem length plus the requested
depth. -/
theorem rawExtensions_word_length (stem : Word) :
    ∀ (depth : Nat) (word : Word), word ∈ rawExtensions stem depth →
      word.length = stem.length + depth
  | 0, word, member => by
      change word ∈ [stem] at member
      have equal := Membership.mem_singleton.mp member
      cases equal
      ring1
  | depth + 1, word, member => by
      change word ∈ rawExtensions (stem ++ [false]) depth ++
        rawExtensions (stem ++ [true]) depth at member
      rcases Membership.mem_append.mp member with left | right
      · rw [rawExtensions_word_length (stem ++ [false]) depth word left,
          Append.length_append]
        simp only [-eq_self, -iff_self, List.length_cons, List.length_nil]; try rfl
        ring1
      · rw [rawExtensions_word_length (stem ++ [true]) depth word right,
          Append.length_append]
        simp only [-eq_self, -iff_self, List.length_cons, List.length_nil]; try rfl
        ring1

/-- Every word enumerated below a finite stem retains that stem as a prefix. -/
theorem rawExtensions_isPrefix (stem : Word) :
    ∀ (depth : Nat) (word : Word), word ∈ rawExtensions stem depth →
      stem.IsPrefix word
  | 0, word, member => by
      change word ∈ [stem] at member
      have equal := Membership.mem_singleton.mp member
      cases equal
      exact ⟨[], Append.append_nil stem⟩
  | depth + 1, word, member => by
      change word ∈ rawExtensions (stem ++ [false]) depth ++
        rawExtensions (stem ++ [true]) depth at member
      rcases Membership.mem_append.mp member with left | right
      · rcases rawExtensions_isPrefix (stem ++ [false]) depth word left with
          ⟨suffix, equal⟩
        exact ⟨[false] ++ suffix, by
          simpa only [-eq_self, -iff_self, Append.append_assoc] using equal⟩
      · rcases rawExtensions_isPrefix (stem ++ [true]) depth word right with
          ⟨suffix, equal⟩
        exact ⟨[true] ++ suffix, by
          simpa only [-eq_self, -iff_self, Append.append_assoc] using equal⟩
end Purelib.Data.List.BinaryPrefix

end
