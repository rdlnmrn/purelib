module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Sort.Key
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.List.Membership

/-!
# Normalized unit-interval cuts

Finite rational requests are filtered to the open unit interval and inserted
into strict order with equal values consolidated. Membership and sortedness
certificates describe the same exact retained normalization procedure.
-/

namespace Purelib.Integration.Partition.Unit.Normalize

open Purelib.Data.List
open Purelib.Data.Rat

public section
/-- Discard cuts outside the open unit interval and insert the remaining values into strictly increasing order.

Repeated cut values are consolidated by the exact rational insertion operation. -/
@[expose] def normalize : List Fraction.Rational → List Fraction.Rational
  | [] => []
  | cut :: tail =>
      if 0 < cut ∧ cut < 1 then Sort.Key.insertRational cut
        (Normalize.normalize tail) else
        Normalize.normalize tail

/-- Normalized unit cuts are strictly increasing. -/
theorem normalize_sorted : ∀ cuts, (normalize cuts).Pairwise (· < ·)
  | [] => List.Pairwise.nil
  | cut :: tail => by
      unfold normalize
      split
      · exact Sort.Key.insertRational_sorted cut
          (Normalize.normalize_sorted
          tail)
      · exact Normalize.normalize_sorted tail

/-- Normalized cuts are exactly the requested values strictly inside the unit interval.

Insertion preserves finite membership and removes repeated equal entries.
The two directions retain the original request membership and both strict bounds. -/
theorem mem_normalize (value : Fraction.Rational) : ∀ cuts,
    value ∈ normalize cuts ↔ value ∈ cuts ∧ 0 < value ∧ value < 1
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨impossible, _⟩
        nomatch impossible
  | cut :: tail => by
      unfold normalize
      by_cases inside : 0 < cut ∧ cut < 1
      · rw [if_pos inside]
        constructor
        · intro member
          rcases (Sort.Key.mem_insertRational cut value (normalize tail)).mp member with atCut |
            inTail
          · subst value
            exact ⟨List.Mem.head tail, inside⟩
          · have retained := (Normalize.mem_normalize value tail).mp inTail
            exact ⟨List.Mem.tail cut retained.1, retained.2⟩
        · rintro ⟨member, bounds⟩
          apply (Sort.Key.mem_insertRational cut value (normalize tail)).mpr
          rcases Membership.mem_cons.mp member with atCut | inTail
          · exact Or.inl atCut
          · exact Or.inr ((Normalize.mem_normalize value tail).mpr ⟨inTail, bounds⟩)
      · rw [if_neg inside]
        constructor
        · intro member
          have retained := (Normalize.mem_normalize value tail).mp member
          exact ⟨List.Mem.tail cut retained.1, retained.2⟩
        · rintro ⟨member, bounds⟩
          rcases Membership.mem_cons.mp member with atCut | inTail
          · exact (inside (atCut ▸ bounds)).elim
          · exact (Normalize.mem_normalize value tail).mpr ⟨inTail, bounds⟩

/-- Normalization preserves an already strictly increasing list of cuts inside the open unit interval. -/
theorem normalize_eq_of_sorted : ∀ {cuts : List Fraction.Rational},
    cuts.Pairwise (· < ·) → (∀ cut ∈ cuts, 0 < cut ∧ cut < 1) → normalize cuts = cuts
  | [], _, _ => rfl
  | head :: tail, sorted, inside => by
      rw [normalize, if_pos (inside head List.mem_cons_self),
        Normalize.normalize_eq_of_sorted (List.pairwise_cons.mp sorted).2
          (fun cut member => inside cut (List.mem_cons_of_mem head member))]
      cases tail with
      | nil => rfl
      | cons next rest =>
          rw [Sort.Key.insertRational, if_pos ((List.pairwise_cons.mp sorted).1 next
            List.mem_cons_self)]

end

end Purelib.Integration.Partition.Unit.Normalize
