module

import Purelib.Data.List.DependentProduct

/-!
# Dependent occurrence-product reduction contracts

These checks run through an ordinary client import. They preserve the original
empty/product shapes at every entry universe and direct bounded lookup of
stored heads and tails, including a family that depends on the original index.
-/

namespace TestPurelib.Data.List.DependentProduct

open Purelib.Data.List (DependentProduct)

universe u v

/-- The empty occurrence product reduces to the original unit in the entry universe. -/
theorem empty_shape {α : Type u} (family : Fin ([] : List α).length → Type v) :
    DependentProduct [] family = PUnit := rfl

/-- The nonempty occurrence product reduces to the original head/tail pair without a universe lift. -/
theorem cons_shape {α : Type u} (head : α) (remaining : List α)
    (family : Fin (head :: remaining).length → Type v) :
    DependentProduct (head :: remaining) family =
      (family 0 × DependentProduct remaining (fun index => family index.succ)) := rfl

/-- Reading an original zero occurrence reduces directly to its stored head. -/
theorem get_zero {α : Type u} (head : α) (remaining : List α)
    (family : Fin (head :: remaining).length → Type v)
    (first : family 0) (tail : DependentProduct remaining (fun index => family index.succ)) :
    DependentProduct.get (head :: remaining) (first, tail) 0 = first := rfl

/-- Reading an original successor occurrence follows the same retained tail and finite index. -/
theorem get_succ {α : Type u} (head : α) (remaining : List α)
    (family : Fin (head :: remaining).length → Type v)
    (first : family 0) (tail : DependentProduct remaining (fun index => family index.succ))
    (index : Fin remaining.length) :
    DependentProduct.get (head :: remaining) (first, tail) index.succ =
      DependentProduct.get remaining tail index := rfl

/-- Materialization retains exactly the supplied head and successor-index tail entries. -/
theorem ofFn_cons {α : Type u} (head : α) (remaining : List α)
    (family : Fin (head :: remaining).length → Type v) (entries : (index : Fin (head :: remaining).length) →
      family index) :
    DependentProduct.ofFn (head :: remaining) entries =
      (entries 0, DependentProduct.ofFn remaining (fun index => entries index.succ)) := rfl

/-- Item-indexed append returns the literal original suffix at every entry universe. -/
theorem append_nil {α : Type u} (family : α → Type v) (second : List α)
    (left : DependentProduct [] (fun index => family (([] : List α)[index.val]'index.isLt)))
    (right : DependentProduct second (fun index => family (second[index.val]'index.isLt))) :
    DependentProduct.append family [] second (fun index => Fin.elim0 index)
      (fun index => second[index.val]'index.isLt) left right = right := rfl

/-- A singleton prefix stores its supplied head and the same complete original suffix cache. -/
theorem append_singleton {α : Type u} (family : α → Type v) (head : α) (second : List α)
    (entry : family head)
    (right : DependentProduct second (fun index => family (second[index.val]'index.isLt))) :
    DependentProduct.append family [head] second (fun _ => head)
      (fun index => second[index.val]'index.isLt) (entry, PUnit.unit) right = (entry, right) := rfl

/-- A singleton append's actual stored tail is the whole original right product, not a materialization. -/
theorem append_singleton_tail {α : Type u} (family : α → Type v) (head : α) (second : List α)
    (entry : family head)
    (right : DependentProduct second (fun index => family (second[index.val]'index.isLt))) :
    (DependentProduct.append family [head] second (fun _ => head)
      (fun index => second[index.val]'index.isLt) (entry, PUnit.unit) right).2 = right := rfl

/-- The original right occurrence remains the identical bounded index when no prefix is present. -/
theorem rightIndex_nil {α : Type u} (second : List α) (index : Fin second.length) :
    DependentProduct.rightIndex [] second index = index := rfl

/-- The first original left occurrence remains the same zero occurrence after append. -/
theorem leftIndex_zero {α : Type u} (head : α) (remaining second : List α) :
    DependentProduct.leftIndex (head :: remaining) second 0 =
      (⟨0, Nat.zero_lt_succ _⟩ : Fin ((head :: remaining) ++ second).length) := rfl

/-- Appended lookup authenticates the whole original left dependent entry at every original bound. -/
theorem appended_left {α : Type u} (family : α → Type v) (first second : List α)
    (left : DependentProduct first (fun index => family (first[index.val]'index.isLt)))
    (right : DependentProduct second (fun index => family (second[index.val]'index.isLt)))
    (index : Fin first.length) :
    HEq (DependentProduct.get (first ++ second) (DependentProduct.append family first second
      (fun index => first[index.val]'index.isLt) (fun index => second[index.val]'index.isLt) left right)
      (DependentProduct.leftIndex first second index)) (DependentProduct.get first left index) :=
  DependentProduct.get_append_left family first second
    (fun index => first[index.val]'index.isLt) (fun index => second[index.val]'index.isLt) left right index

/-- Appended lookup authenticates the whole original right dependent entry at every original bound. -/
theorem appended_right {α : Type u} (family : α → Type v) (first second : List α)
    (left : DependentProduct first (fun index => family (first[index.val]'index.isLt)))
    (right : DependentProduct second (fun index => family (second[index.val]'index.isLt)))
    (index : Fin second.length) :
    HEq (DependentProduct.get (first ++ second) (DependentProduct.append family first second
      (fun index => first[index.val]'index.isLt) (fun index => second[index.val]'index.isLt) left right)
      (DependentProduct.rightIndex first second index)) (DependentProduct.get second right index) :=
  DependentProduct.get_append_right family first second
    (fun index => first[index.val]'index.isLt) (fun index => second[index.val]'index.isLt) left right index

/-- Arbitrary actual interpreted coordinates retain the complete supplied right product at the empty prefix. -/
theorem append_values_nil {α β : Type u} (family : β → Type v) (second : List α)
    (leftValues : Fin ([] : List α).length → β) (rightValues : Fin second.length → β)
    (left : DependentProduct [] (fun index => family (leftValues index)))
    (right : DependentProduct second (fun index => family (rightValues index))) :
    DependentProduct.append family [] second leftValues rightValues left right = right := rfl

/-- Actual coordinate append never substitutes the underlying list item for a retained interpreted channel. -/
theorem append_values_singleton {α β : Type u} (family : β → Type v) (head : α) (second : List α)
    (value : β) (rightValues : Fin second.length → β) (entry : family value)
    (right : DependentProduct second (fun index => family (rightValues index))) :
    DependentProduct.append family [head] second (fun _ => value) rightValues (entry, PUnit.unit) right =
      (entry, right) := rfl

/-- Reflexive finite-family transport preserves the complete actual original product at every list and universe. -/
theorem transport_refl {α : Type u} : (items : List α) → (family : Fin items.length → Type v) →
    (entries : DependentProduct items family) →
    DependentProduct.transport items (fun _ => rfl) entries = entries
  | [], _, _ => rfl
  | head :: remaining, family, entries => by
      rewrite [DependentProduct.transport_cons]
      exact congrArg (fun tail => (entries.1, tail))
        (transport_refl remaining (fun index => family index.succ) entries.2)

end TestPurelib.Data.List.DependentProduct
