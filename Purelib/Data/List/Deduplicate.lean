module
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.List.Membership

import Purelib.Tactic.QuotientFreeOmega

/-!
# Last-occurrence Gaussian duplicate removal

The original recursion discards a head already present in its tail. The
lawful Boolean equality scan retains the same branch and the same ordered
last occurrences, with direct occurrence and length certificates.
-/
namespace Purelib.Data.List.Deduplicate

open Purelib.Data.Gaussian.Basic

/-- Remove repeated Gaussian-rational entries while retaining their final occurrences.

The recursion discards a head already present in the remaining tail and otherwise
retains it. Executable equality determines membership, and the order of retained
final occurrences is preserved. -/
@[expose] public def deduplicateCandidates : List Canonical → List Canonical
  | [] => []
  | candidate :: remaining =>
      if candidate ∈ remaining then
        deduplicateCandidates remaining
      else
        candidate :: deduplicateCandidates remaining

open Purelib.Data.List
/-- Duplicate removal preserves the original Gaussian-rational members.

Each retained tail occurrence transports by the recursive certificate. A duplicate
head already has its tail occurrence; a fresh head keeps its original constructor. -/
public theorem mem_deduplicateCandidates (candidate : Canonical) :
    (values : List Canonical) →
      candidate ∈ deduplicateCandidates values ↔ candidate ∈ values
  | [] => by
      constructor
      · intro impossible; nomatch impossible
      · intro impossible; nomatch impossible
  | value :: remaining => by
      rw [deduplicateCandidates]
      split
      · rename_i duplicate
        constructor
        · intro retained
          exact List.Mem.tail value ((mem_deduplicateCandidates candidate remaining).mp retained)
        · intro source
          cases source with
          | head => exact (mem_deduplicateCandidates candidate remaining).mpr duplicate
          | tail _ retained => exact (mem_deduplicateCandidates candidate remaining).mpr retained
      · constructor
        · intro retained
          cases retained with
          | head => exact List.Mem.head remaining
          | tail _ retained =>
              exact List.Mem.tail value ((mem_deduplicateCandidates candidate remaining).mp retained)
        · intro source
          cases source with
          | head => exact List.Mem.head _
          | tail _ retained =>
              exact List.Mem.tail value ((mem_deduplicateCandidates candidate remaining).mpr retained)

/-- Removing repeated Gaussian-rational entries never increases the list length. -/
public theorem deduplicateCandidates_length_le (values : List Canonical) :
    (deduplicateCandidates values).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons value remaining inductionHypothesis =>
      rw [deduplicateCandidates]
      split
      · exact Nat.le_succ_of_le inductionHypothesis
      · exact Nat.succ_le_succ inductionHypothesis
end Purelib.Data.List.Deduplicate
