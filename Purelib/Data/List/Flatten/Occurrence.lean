module

import Purelib.Data.List.Append
import Purelib.Data.Nat.Subtraction

/-! # Original bounded occurrences in ordered finite block concatenations

A bounded flattened position determines its original block and local position
by following the displayed append lengths. The returned offset identity keeps
ordered occurrences distinct even when several entries have equal values.
No membership witness, coordinate search or choice selects an occurrence.
-/

public section

namespace Purelib.Data.List.Flatten

open Purelib.Data.List
open Purelib.Data.Nat

universe u

variable {Item : Type u}

/-- An original block/local occurrence with its exact flattened value and prefix-offset identities.

The original flattened position is retained as an index. The outer and
inner bounded positions follow the displayed block spine, preserving
repeated entries and empty intervening blocks without identifying them.
-/
@[expose] def Occurrence (blocks : List (List Item)) (index : Fin blocks.flatten.length) :=
  (outer : Fin blocks.length) ×
  { inner : Fin (blocks[outer.val]'outer.isLt).length //
    blocks.flatten[index.val]'index.isLt = (blocks[outer.val]'outer.isLt)[inner.val]'inner.isLt ∧
      index.val = (blocks.take outer.val).flatten.length + inner.val }

/-- Locate the exact original block and local index of an actual bounded flattened occurrence.

A left occurrence retains its natural index. A right occurrence subtracts
only the actual first block length and recurses on the unchanged tail.
Both the actual value equality and full prefix offset are derived internally.
-/
def locate : (blocks : List (List Item)) → (index : Fin blocks.flatten.length) → Occurrence blocks index
  | [], index => Fin.elim0 index
  | head :: remaining, index =>
      if inside : index.val < head.length then
        ⟨0, ⟨⟨index.val, inside⟩,
          Append.getElem_append_left head remaining.flatten index.val inside index.isLt,
          (Nat.zero_add index.val).symm⟩⟩
      else
        have after : head.length ≤ index.val := Nat.le_of_not_lt inside
        have bounded : index.val - head.length < remaining.flatten.length := by
          have actual := index.isLt
          change index.val < (head ++ remaining.flatten).length at actual
          rewrite [Append.length_append] at actual
          exact Subtraction.sub_lt_left_of_lt_add after actual
        let localIndex : Fin remaining.flatten.length := ⟨index.val - head.length, bounded⟩
        let found := locate remaining localIndex
        have offset : index.val = head.length + localIndex.val := (Subtraction.add_sub_of_le after).symm
        have combinedBound : head.length + localIndex.val < (head ++ remaining.flatten).length := by
          rewrite [← offset]
          exact index.isLt
        have selected : (head ++ remaining.flatten)[index.val]'index.isLt =
            remaining.flatten[localIndex.val]'localIndex.isLt :=
          (getElem_congr rfl offset index.isLt).trans
            (Append.getElem_append_right head remaining.flatten localIndex.val localIndex.isLt combinedBound)
        have prefixLength : ((head :: remaining).take found.1.succ.val).flatten.length =
            head.length + (remaining.take found.1.val).flatten.length := by
          change (head ++ (remaining.take found.1.val).flatten).length = _
          exact Append.length_append _ _
        ⟨found.1.succ, ⟨found.2.val, selected.trans found.2.property.1, by
          calc
            index.val = head.length + localIndex.val := offset
            _ = head.length + ((remaining.take found.1.val).flatten.length + found.2.val.val) :=
              congrArg (fun count => head.length + count) found.2.property.2
            _ = (head.length + (remaining.take found.1.val).flatten.length) + found.2.val.val :=
              (Nat.add_assoc _ _ _).symm
            _ = _ := congrArg (fun count => count + found.2.val.val) prefixLength.symm⟩⟩
termination_by structural blocks _ => blocks

/-- Embed an original block/local occurrence into its exact flattened occurrence with both readbacks.

The constructor follows the retained block spine and shifts by each actual
preceding length. It does not run locate, compare item values or choose an
occurrence from membership evidence.
-/
def position : (blocks : List (List Item)) → (outer : Fin blocks.length) →
    (inner : Fin (blocks[outer.val]'outer.isLt).length) →
    { index : Fin blocks.flatten.length //
      blocks.flatten[index.val]'index.isLt = (blocks[outer.val]'outer.isLt)[inner.val]'inner.isLt ∧
      index.val = (blocks.take outer.val).flatten.length + inner.val }
  | [], outer, _ => Fin.elim0 outer
  | head :: remaining, ⟨0, _⟩, inner => by
      have combined : inner.val < (head ++ remaining.flatten).length := by
        rewrite [Append.length_append]
        exact Nat.lt_of_lt_of_le inner.isLt (Nat.le_add_right head.length remaining.flatten.length)
      exact ⟨⟨inner.val, combined⟩,
        Append.getElem_append_left head remaining.flatten inner.val inner.isLt combined,
        (Nat.zero_add inner.val).symm⟩
  | head :: remaining, ⟨value + 1, bound⟩, inner => by
      let outer : Fin remaining.length := ⟨value, Nat.lt_of_succ_lt_succ bound⟩
      let found := position remaining outer inner
      have combined : head.length + found.val.val < (head ++ remaining.flatten).length := by
        rewrite [Append.length_append]
        exact Nat.add_lt_add_left found.val.isLt head.length
      have prefix_length : ((head :: remaining).take (value + 1)).flatten.length =
          head.length + (remaining.take value).flatten.length := Append.length_append _ _
      refine ⟨⟨head.length + found.val.val, combined⟩, ?_, ?_⟩
      · exact (Append.getElem_append_right head remaining.flatten found.val.val found.val.isLt combined).trans
          found.property.1
      · calc
          head.length + found.val.val =
              head.length + ((remaining.take value).flatten.length + inner.val) :=
            congrArg (fun index => head.length + index) found.property.2
          _ = (head.length + (remaining.take value).flatten.length) + inner.val :=
            (Nat.add_assoc _ _ _).symm
          _ = _ := congrArg (fun index => index + inner.val) prefix_length.symm
termination_by structural blocks _ _ => blocks

end Purelib.Data.List.Flatten

end
