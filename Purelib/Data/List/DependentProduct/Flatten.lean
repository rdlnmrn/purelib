module

public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Append

/-! # Ordered concatenation of retained item-dependent products

Only the original stored heads and tails are consumed. Empty blocks remain
part of the original outer product; concatenation changes neither an entry
value nor its mathematical item owner.
-/

public section

namespace Purelib.Data.List.DependentProduct

universe u v w

variable {Item : Type u} {family : Item → Type v}

/-- Exact item-list identity preserves the same entry family at the transported finite positions. -/
theorem castItems_family {first last : List Item} (equal : last = first) :
    (fun index : Fin last.length => family (first[index.val]'(by rewrite [← equal]; exact index.isLt))) =
      (fun index : Fin last.length => family (last[index.val]'index.isLt)) := by
  cases equal
  rfl

/-- Append the exact stored item-dependent heads and tails, without invoking any entry-producing function. -/
@[expose] def appendItems : (first last : List Item) →
    DependentProduct first (fun index => family (first[index.val]'index.isLt)) →
    DependentProduct last (fun index => family (last[index.val]'index.isLt)) →
    DependentProduct (first ++ last) (fun index => family ((first ++ last)[index.val]'index.isLt))
  | [], _, _, after => after
  | _ :: tail, last, before, after => (before.1, appendItems tail last before.2 after)

/-- Flatten actual stored products in original block/local order, preserving empty blocks in the retained input. -/
@[expose] def flattenItems : (blocks : List (List Item)) →
    DependentProduct blocks (fun outer =>
      DependentProduct (blocks[outer.val]'outer.isLt)
        (fun inner => family ((blocks[outer.val]'outer.isLt)[inner.val]'inner.isLt))) →
    DependentProduct blocks.flatten (fun index => family (blocks.flatten[index.val]'index.isLt))
  | [], _ => PUnit.unit
  | head :: tail, entries => appendItems head tail.flatten entries.1 (flattenItems tail entries.2)

/-- Item-index-only natural weights have the same sum on any two actual retained entry products. -/
theorem sum_independent {Entry : Type u} : (items : List Entry) →
    {firstFamily : Fin items.length → Type v} → {lastFamily : Fin items.length → Type w} →
    (first : DependentProduct items firstFamily) → (last : DependentProduct items lastFamily) →
    (weight : Fin items.length → Nat) →
    sum items (fun index _actual => weight index) first =
      sum items (fun index _actual => weight index) last
  | [], _, _, _, _, _ => rfl
  | _ :: tail, _, _, first, last, weight =>
      congrArg (Nat.add (weight 0)) (sum_independent tail first.2 last.2 (fun index => weight index.succ))

/-- The original block lengths sum to the exact flattened length on every retained outer product. -/
theorem sum_lengths : (blocks : List (List Item)) → {payload : Fin blocks.length → Type w} →
    (entries : DependentProduct blocks payload) →
    sum blocks (fun index _actual => (blocks[index.val]'index.isLt).length) entries = blocks.flatten.length
  | [], _, _ => rfl
  | head :: tail, _, entries =>
      (congrArg (Nat.add head.length) (sum_lengths tail entries.2)).trans
        (Append.length_append head tail.flatten).symm

/-- Sum natural weights of the actual stored item-dependent entries in their original order. -/
@[expose] def sumItems (items : List Item)
    (entries : DependentProduct items (fun index => family (items[index.val]'index.isLt)))
    (weight : (item : Item) → family item → Nat) : Nat :=
  sum items (fun index actual => weight (items[index.val]'index.isLt) actual) entries

/-- Exact whole-item-list transport preserves the natural weight sum of the SAME retained entries. -/
theorem sumItems_castItems {first last : List Item} (equal : first = last)
    (entries : DependentProduct first (fun index => family (first[index.val]'index.isLt)))
    (weight : (item : Item) → family item → Nat) :
    sumItems last (castItems equal.symm entries
      (resultFamily := fun index => family (last[index.val]'index.isLt))
      (sameFamily := by cases equal; rfl)) weight = sumItems first entries weight := by
  cases equal
  rfl

/-- Appending actual retained products adds their natural weight sums without selecting entries again. -/
theorem sumItems_appendItems : (first last : List Item) →
    (before : DependentProduct first (fun index => family (first[index.val]'index.isLt))) →
    (after : DependentProduct last (fun index => family (last[index.val]'index.isLt))) →
    (weight : (item : Item) → family item → Nat) →
    sumItems (first ++ last) (appendItems first last before after) weight =
      sumItems first before weight + sumItems last after weight
  | [], _, _, _, _ => (Nat.zero_add _).symm
  | head :: tail, last, before, after, weight => by
      change weight head before.1 + sumItems (tail ++ last) (appendItems tail last before.2 after) weight =
        (weight head before.1 + sumItems tail before.2 weight) + sumItems last after weight
      exact (congrArg (fun total => weight head before.1 + total)
        (sumItems_appendItems tail last before.2 after weight)).trans ((Nat.add_assoc _ _ _).symm)

/-- Flattening SAME stored blocks preserves their original nested natural weight sum, including empty blocks. -/
theorem sumItems_flattenItems : (blocks : List (List Item)) →
    (entries : DependentProduct blocks (fun outer =>
      DependentProduct (blocks[outer.val]'outer.isLt)
        (fun inner => family ((blocks[outer.val]'outer.isLt)[inner.val]'inner.isLt)))) →
    (weight : (item : Item) → family item → Nat) →
    sumItems blocks.flatten (flattenItems blocks entries) weight =
      sum blocks (fun outer actual => sumItems (blocks[outer.val]'outer.isLt) actual weight) entries
  | [], _, _ => rfl
  | head :: tail, entries, weight =>
      (sumItems_appendItems head tail.flatten entries.1 (flattenItems tail entries.2) weight).trans
        (congrArg (fun total => sumItems head entries.1 weight + total)
          (sumItems_flattenItems tail entries.2 weight))

end Purelib.Data.List.DependentProduct

end
