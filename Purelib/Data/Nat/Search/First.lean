module

import Lean.Elab.Tactic.Omega
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded first-satisfying natural search

A supplied terminal witness bounds the first satisfying index. The finite
scan retains every earlier predicate failure within the original interval.
-/

public section

namespace Purelib.Data.Nat.Search.First

set_option genInjectivity false in
/-- A first satisfying natural index at or beyond a supplied start.

The record retains the selected exponent, its lower bound and predicate proof, and a
refutation of the predicate at every earlier index from the same start. -/
structure FirstResult (predicate : Nat → Prop) (start : Nat) where
  /-- The first accepted index in the displayed search interval. -/ exponent : Nat
  /-- The selected index is at or beyond the starting index. -/ start_le : start ≤ exponent
  /-- The searched predicate holds at the selected index. -/ holds : predicate exponent
  /-- The predicate fails at each index from the start up to the selected index. -/ before_fails : ∀ index, start ≤
    index → index < exponent →
    ¬predicate index

constructive_injectivity FirstResult

/-- Scan a bounded natural interval for its first true predicate value.

A supplied terminal witness guarantees success before fuel exhaustion. The returned
certificate records the selected index, its lower bound, and failure at every
preceding index in the interval. -/
@[expose] def scanFirst (predicate : Nat → Prop)
    (decidablePredicate : (index : Nat) → Decidable (predicate index)) :
    (start fuel : Nat) → predicate (start + fuel) →
      FirstResult predicate start
  | start, 0, terminalHolds =>
      ⟨start, Nat.le_refl start, by
        simpa only [Nat.add_zero] using terminalHolds,
        by
          intro index startLe indexLt
          exact (Nat.not_lt_of_ge startLe indexLt).elim⟩
  | start, fuel + 1, terminalHolds =>
      if startHolds : predicate start then
        ⟨start, Nat.le_refl start, startHolds,
          by
            intro index startLe indexLt
            exact (Nat.not_lt_of_ge startLe indexLt).elim⟩
      else
        let result := Purelib.Data.Nat.Search.First.scanFirst predicate decidablePredicate (start + 1) fuel
          (by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              terminalHolds)
        ⟨result.exponent,
          Nat.le_trans (Nat.le_succ start) result.start_le,
          result.holds,
          by
            intro index startLe indexLt
            by_cases atStart : index = start
            · simpa only [atStart] using startHolds
            · have startLt : start < index :=
                Nat.lt_of_le_of_ne startLe (Ne.symm atStart)
              exact result.before_fails index
                (Nat.succ_le_of_lt startLt) indexLt⟩
end Purelib.Data.Nat.Search.First

end
