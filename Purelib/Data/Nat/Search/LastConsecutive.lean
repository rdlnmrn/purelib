module

import Lean.Elab.Tactic.Omega
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded last-consecutive natural search

A supplied terminal failure bounds a consecutive run of satisfying indices.
The finite scan retains the last accepted index and its immediate next failure.
-/

public section

namespace Purelib.Data.Nat.Search.LastConsecutive

set_option genInjectivity false in
/-- A satisfying natural index whose immediate successor fails the predicate.

The retained exponent is at least the supplied start. The record certifies the
predicate at that exponent and its failure at the next index; it makes no claim about
later disconnected satisfying indices. -/
structure LastResult (predicate : Nat → Prop) (start : Nat) where
  /-- The final accepted index before the next predicate failure. -/ exponent : Nat
  /-- The selected index is at or beyond the starting index. -/ start_le : start ≤ exponent
  /-- The predicate holds at the selected index. -/ holds : predicate exponent
  /-- The predicate fails at the immediate successor of the selected index. -/ next_fails : ¬predicate (exponent + 1)

constructive_injectivity LastResult

/-- Scan forward from a true value until the next predicate value is false.

A terminal failure bounds execution. The result retains a true index at or beyond the
starting point together with failure at its immediate successor. -/
@[expose] def scanLast (predicate : Nat → Prop)
    (decidablePredicate : (index : Nat) → Decidable (predicate index)) :
    (start fuel : Nat) → predicate start →
      ¬predicate (start + fuel + 1) → LastResult predicate start
  | start, 0, startHolds, terminalFailure =>
      ⟨start, Nat.le_refl start, startHolds, by
        simpa only [Nat.add_zero] using terminalFailure⟩
  | start, fuel + 1, startHolds, terminalFailure =>
      if nextHolds : predicate (start + 1) then
        let result := Purelib.Data.Nat.Search.LastConsecutive.scanLast predicate decidablePredicate (start + 1) fuel
          nextHolds (by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              terminalFailure)
        ⟨result.exponent,
          Nat.le_trans (Nat.le_succ start) result.start_le,
          result.holds,
          result.next_fails⟩
      else
        ⟨start, Nat.le_refl start, startHolds, nextHolds⟩
end Purelib.Data.Nat.Search.LastConsecutive

end
