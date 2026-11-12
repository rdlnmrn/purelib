module

public import Init.Data.List.OfFn
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Append

/-! # Original finite tables grouped by retained block positions

The full prefix offsets identify every original position in a flattened
finite word. Re-grouping the original indexed values preserves the complete
ordered table, including repeated values and empty blocks.
-/

public section

namespace Purelib.Data.List.Flatten

open Purelib.Data.List

universe u v

variable {Item : Type u} {Value : Type v}

/-- Group the original indexed table by exact original block/local prefix positions.

The supplied positions retain the original global bound. Their complete
prefix offsets, rather than equality of selected values, identify all
occurrences. The conclusion is equality of the whole ordered value lists;
no factory producing a value is invoked by this proof.
-/
theorem ofFn_grouped {blockCount count : Nat} (blocks : Fin blockCount → List Item)
    (length_eq : count = (List.ofFn blocks).flatten.length) (values : Fin count → Value)
    (positions : (outer : Fin blockCount) → Fin (blocks outer).length → Fin count)
    (offset : ∀ outer inner,
      (positions outer inner).val = ((List.ofFn blocks).take outer.val).flatten.length + inner.val) :
    List.ofFn values =
      (List.ofFn (fun outer => List.ofFn (fun inner => values (positions outer inner)))).flatten := by
  induction blockCount generalizing count with
  | zero =>
      have zero : count = 0 := length_eq
      cases zero
      rfl
  | succ blockCount previous =>
      let head := blocks 0
      let remaining := fun index : Fin blockCount => blocks index.succ
      have words : List.ofFn blocks = head :: List.ofFn remaining := OfFn.Basic.ofFn_succ
      have size_eq : count = head.length + (List.ofFn remaining).flatten.length :=
        length_eq.trans ((congrArg (fun word => word.flatten.length) words).trans
          (Append.length_append head (List.ofFn remaining).flatten))
      cases size_eq
      let tailPositions : (outer : Fin blockCount) →
          Fin (remaining outer).length → Fin (List.ofFn remaining).flatten.length := by
        intro outer inner
        have original := offset outer.succ inner
        have prefix_length : ((List.ofFn blocks).take outer.succ.val).flatten.length =
            head.length + ((List.ofFn remaining).take outer.val).flatten.length := by
          rewrite [words]
          exact Append.length_append _ _
        have selected : (positions outer.succ inner).val =
            head.length + (((List.ofFn remaining).take outer.val).flatten.length + inner.val) :=
          original.trans ((congrArg (fun length => length + inner.val) prefix_length).trans
            (Nat.add_assoc _ _ _))
        have bounded : head.length + (((List.ofFn remaining).take outer.val).flatten.length + inner.val) <
            head.length + (List.ofFn remaining).flatten.length :=
          Eq.mp (congrArg (fun value => value < head.length + (List.ofFn remaining).flatten.length) selected)
            (positions outer.succ inner).isLt
        exact ⟨((List.ofFn remaining).take outer.val).flatten.length + inner.val,
          Nat.lt_of_add_lt_add_left bounded⟩
      let tailValues : Fin (List.ofFn remaining).flatten.length → Value :=
        fun index => values (index.natAdd head.length)
      have tailOffsets (outer : Fin blockCount) (inner : Fin (remaining outer).length) :
          (tailPositions outer inner).val =
            ((List.ofFn remaining).take outer.val).flatten.length + inner.val := by
        rfl
      have tail_eq := previous remaining rfl tailValues tailPositions tailOffsets
      have tailTable :
          List.ofFn (fun outer : Fin blockCount =>
            List.ofFn (fun inner => tailValues (tailPositions outer inner))) =
          List.ofFn (fun outer : Fin blockCount =>
            List.ofFn (fun inner => values (positions outer.succ inner))) := by
        apply OfFn.Basic.ofFn_congr
        intro outer
        apply OfFn.Basic.ofFn_congr
        intro inner
        apply congrArg values
        apply Fin.ext
        change head.length + (tailPositions outer inner).val = (positions outer.succ inner).val
        have prefix_length : ((List.ofFn blocks).take outer.succ.val).flatten.length =
            head.length + ((List.ofFn remaining).take outer.val).flatten.length := by
          rewrite [words]
          exact Append.length_append _ _
        exact ((offset outer.succ inner).trans
          ((congrArg (fun length => length + inner.val) prefix_length).trans (Nat.add_assoc _ _ _))).symm
      have headTable :
          List.ofFn (fun index : Fin head.length =>
            values (index.castLE (Nat.le_add_right head.length (List.ofFn remaining).flatten.length))) =
          List.ofFn (fun inner => values (positions 0 inner)) := by
        apply OfFn.Basic.ofFn_congr
        intro inner
        apply congrArg values
        apply Fin.ext
        exact ((offset 0 inner).trans (Nat.zero_add inner.val)).symm
      calc
        List.ofFn values =
            List.ofFn (fun index : Fin head.length =>
              values (index.castLE (Nat.le_add_right head.length (List.ofFn remaining).flatten.length))) ++
            List.ofFn tailValues := OfFn.Basic.ofFn_add
        _ = List.ofFn (fun inner => values (positions 0 inner)) ++
            (List.ofFn (fun outer : Fin blockCount =>
              List.ofFn (fun inner => values (positions outer.succ inner)))).flatten := by
          rewrite [headTable, tail_eq, tailTable]
          rfl
        _ = _ := by
          rewrite [OfFn.Basic.ofFn_succ]
          rfl

end Purelib.Data.List.Flatten

end
