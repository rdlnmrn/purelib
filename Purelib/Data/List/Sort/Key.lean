module

-- Public insertion and ordering certificates retain the original fraction/order owners.
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Ordered rational insertion with equality removal

Insertion scans the original rational list until the new cut is smaller than or
identical to its head. Membership and strict pairwise ordering are certified
from the original list constructors and direct canonical rational comparisons.
-/

section

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

namespace Purelib.Data.List.Sort.Key
/-- Insert a rational cut into a list without adding another equal occurrence.

The original smaller comparison inserts the cut before the head. Equality retains
that head; otherwise the same tail is scanned and the head is retained unchanged. -/
@[expose] public def insertRational (cut : Rational) : List Rational → List Rational
  | [] => [cut]
  | head :: tail =>
      if cut < head then cut :: head :: tail
      else if cut = head then head :: tail
      else head :: Purelib.Data.List.Sort.Key.insertRational cut tail
/-- Insertion retains exactly the original list members and the supplied cut.

The equivalence follows each original comparison branch. List membership is
transported through its constructors, so equality removal keeps the same member. -/
public theorem mem_insertRational (cut value : Rational) : ∀ cuts,
    value ∈ Purelib.Data.List.Sort.Key.insertRational cut cuts ↔ value = cut ∨ value ∈ cuts
  | [] => by
      constructor
      · intro member
        cases member with
        | head => exact Or.inl rfl
        | tail _ impossible => nomatch impossible
      · intro member
        rcases member with atCut | impossible
        · cases atCut
          exact List.Mem.head []
        · nomatch impossible
  | head :: tail => by
      unfold Purelib.Data.List.Sort.Key.insertRational
      by_cases before : cut < head
      · rewrite [if_pos before]
        constructor
        · intro member
          cases member with
          | head => exact Or.inl rfl
          | tail _ old => exact Or.inr old
        · intro member
          rcases member with atCut | old
          · cases atCut
            exact List.Mem.head _
          · exact List.Mem.tail cut old
      · rewrite [if_neg before]
        by_cases equal : cut = head
        · rewrite [if_pos equal]
          constructor
          · exact Or.inr
          · intro member
            rcases member with atCut | old
            · have atHead : value = head := atCut.trans equal
              cases atHead
              exact List.Mem.head tail
            · exact old
        · rewrite [if_neg equal]
          constructor
          · intro member
            cases member with
            | head => exact Or.inr (List.Mem.head tail)
            | tail _ inInserted =>
                rcases (Purelib.Data.List.Sort.Key.mem_insertRational cut value tail).mp inInserted with atCut | old
                · exact Or.inl atCut
                · exact Or.inr (List.Mem.tail head old)
          · intro member
            rcases member with atCut | old
            · exact List.Mem.tail head ((Purelib.Data.List.Sort.Key.mem_insertRational cut value tail).mpr (Or.inl
              atCut))
            · cases old with
              | head => exact List.Mem.head _
              | tail _ inTail =>
                  exact List.Mem.tail head ((Purelib.Data.List.Sort.Key.mem_insertRational cut value tail).mpr (Or.inr
                    inTail))
/-- Rational insertion with equality removal preserves strict pairwise ordering.

Each earlier original entry is strictly below every later entry. The inserted
cut is related directly to the head and retained tail by asymmetric weak bounds. -/
public theorem insertRational_sorted (cut : Rational) : ∀ {cuts},
    cuts.Pairwise (· < ·) → (Purelib.Data.List.Sort.Key.insertRational cut cuts).Pairwise (· < ·)
  | [], _ => List.Pairwise.cons (fun _ impossible => nomatch impossible) List.Pairwise.nil
  | head :: tail, sorted => by
      unfold Purelib.Data.List.Sort.Key.insertRational
      cases sorted with
      | cons headRelated tailSorted =>
          by_cases before : cut < head
          · rewrite [if_pos before]
            apply List.Pairwise.cons
            · intro value member
              cases member with
              | head => exact before
              | tail _ inTail =>
                  have retained : head < value := headRelated value inTail
                  exact ⟨Rat.Fraction.Order.Basic.le_trans cut head value before.1 retained.1,
                    fun reverse => before.2
                      (Rat.Fraction.Order.Basic.le_trans head value cut retained.1 reverse)⟩
            · exact List.Pairwise.cons headRelated tailSorted
          · rewrite [if_neg before]
            by_cases equal : cut = head
            · rewrite [if_pos equal]
              exact List.Pairwise.cons headRelated tailSorted
            · rewrite [if_neg equal]
              apply List.Pairwise.cons
              · have headLe : head ≤ cut := Arithmetic.le_of_not_gt_direct before
                have headLess : head < cut :=
                  ⟨headLe, fun reverse => equal
                    (Basic.Compatibility.le_antisymm cut head reverse headLe)⟩
                intro value member
                rcases (Purelib.Data.List.Sort.Key.mem_insertRational cut value tail).mp member with atCut | inTail
                · cases atCut
                  exact headLess
                · exact headRelated value inTail
              · exact Purelib.Data.List.Sort.Key.insertRational_sorted cut tailSorted
end Purelib.Data.List.Sort.Key

end
