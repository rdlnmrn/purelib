module

public import Purelib.Polynomial.Dense.Roots.Word
public import Init.Data.List.OfFn
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Filter
import Purelib.Data.List.CountWhere
import Purelib.Data.List.Replicate
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained selections of original root-block coordinates

One Boolean label is retained at each original bounded block. Filtering the
same original expanded word preserves every selected block's multiplicity
and order. The selected coordinate count is the corresponding weighted
finite fold; no geometric interpretation of the labels is asserted here.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Word

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*}

/-- Sum original block multiplicities at precisely the retained true labels. -/
@[expose] def weight (blocks : List (Block K)) (labels : Vec Bool blocks.length) : Nat :=
  (List.ofFn fun index : Fin blocks.length =>
    if labels index then (blocks[index.val]'index.isLt).multiplicity else 0).foldr Nat.add 0

/-- Filtering the original expanded word has the exact multiplicity-weighted selected length. -/
theorem length_filter (blocks : List (Block K)) (labels : Vec Bool blocks.length) :
    ((expand blocks).filter fun index => labels index).length = weight blocks labels := by
  induction blocks with
  | nil => cases labels; rfl
  | cons block tail previous =>
      cases labels with
      | cons selected remaining =>
          rw [expand, Filter.filter_append, Append.length_append, Filter.filter_replicate]
          have tailLength :
              (((expand tail).map Fin.succ).filter fun index => (Vec.cons selected remaining) index).length =
                ((expand tail).filter fun index => remaining index).length :=
            CountWhere.listCountWhere_map (expand tail) Fin.succ (fun index => (Vec.cons selected remaining) index)
          refine (congrArg (fun count : Nat =>
            (if selected then List.replicate block.multiplicity (0 : Fin (tail.length + 1)) else []).length + count)
              (tailLength.trans (previous remaining))).trans ?_
          unfold weight
          rw [OfFn.Basic.ofFn_succ, List.foldr_cons]
          cases selected with
          | false => rfl
          | true =>
              change (List.replicate block.multiplicity (0 : Fin (tail.length + 1))).length + _ =
                block.multiplicity + _
              rw [Replicate.length_replicate]
              rfl

set_option genInjectivity false in
/-- The original block labels and their actual selected coordinate word with certified multiplicity count.

The complete expanded word is cached once. The selected word is the original
Boolean filter of that same cache, retaining original bounded block indices
and every accepted occurrence. Its count and occurrence bounds are proved
from those actual data, rather than supplied as rank or basis premises.
-/
structure Selection [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K} (bank : Bank polynomial) where
  /-- The actual retained original block labels. -/
  labels : Vec Bool bank.blocks.length
  /-- The one cached complete original block-coordinate word. -/
  fullWord : List (Fin bank.blocks.length)
  /-- The full cache uses the original multiplicity expansion. -/
  fullWord_eq : fullWord = expand bank.blocks
  /-- The actual selected original coordinate indices. -/
  word : List (Fin bank.blocks.length)
  /-- Selection preserves the original full-word order and all true-labelled occurrences. -/
  word_eq : word = fullWord.filter (fun index => labels index)
  /-- The actual multiplicity-weighted selected coordinate count. -/
  count : Nat
  /-- The same original block labels determine this finite weighted fold. -/
  count_eq : count = weight bank.blocks labels
  /-- The selected original word has exactly that computed coordinate count. -/
  length_eq : word.length = count
  /-- Every selected original occurrence stays below its same original block multiplicity. -/
  admissible : ∀ column : Fin word.length,
    countBefore (word[column.val]'column.isLt) word column.val <
      (bank.block (word[column.val]'column.isLt)).multiplicity

constructive_injectivity Selection

namespace Selection

variable [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}

/-- Every original block retains its full multiplicity when selected and contributes no occurrence otherwise. -/
theorem count_occurrences (retained : Selection bank) (index : Fin bank.blocks.length) :
    countBefore index retained.word retained.word.length =
      if retained.labels index then (bank.block index).multiplicity else 0 := by
  rw [retained.word_eq, countBefore_filter, retained.fullWord_eq, Word.count]
  rfl

/-- Every selected original occurrence carries a true label at its same original block index. -/
theorem accepted (retained : Selection bank) (column : Fin retained.word.length) :
    retained.labels (retained.word[column.val]'column.isLt) = true := by
  let original := retained.word[column.val]'column.isLt
  have strict := countBefore_lt_total retained.word column
  change countBefore original retained.word column.val <
    countBefore original retained.word retained.word.length at strict
  rw [retained.count_occurrences original] at strict
  cases chosen : retained.labels original with
  | false =>
      rw [chosen] at strict
      exact (Nat.not_lt_zero _ strict).elim
  | true => rfl

/-- Every occurrence cache of the same selected word retains orders below the original multiplicities. -/
theorem order_lt (retained : Selection bank) (occurrences : Occurrences retained.word)
    (column : Fin retained.word.length) :
    occurrences.orders column < (bank.block (retained.word[column.val]'column.isLt)).multiplicity := by
  rw [occurrences.order_spec]
  exact retained.admissible column

/-- Compute the actual selected original coordinate word and all its finite certificates.

The original multiplicity expansion and its Boolean filter are each computed
once. The corresponding original weighted fold is retained alongside exact
length and occurrence-order readbacks.
-/
@[expose] def prepare (bank : Bank polynomial) (labels : Vec Bool bank.blocks.length) : Selection bank := by
  let fullWord := expand bank.blocks
  let word := fullWord.filter fun index => labels index
  let count := weight bank.blocks labels
  have admissible : ∀ column : Fin word.length,
      countBefore (word[column.val]'column.isLt) word column.val <
        (bank.block (word[column.val]'column.isLt)).multiplicity := by
    intro column
    let original := word[column.val]'column.isLt
    have strict := countBefore_lt_total word column
    change countBefore original word column.val < countBefore original word word.length at strict
    have occurrences : countBefore original word word.length =
        if labels original then (bank.block original).multiplicity else 0 := by
      rw [countBefore_filter, Word.count]
      rfl
    rw [occurrences] at strict
    cases chosen : labels original with
    | false =>
        rw [chosen] at strict
        exact (Nat.not_lt_zero _ strict).elim
    | true =>
        rw [chosen] at strict
        exact strict
  exact
    { labels := labels
      fullWord := fullWord
      fullWord_eq := rfl
      word := word
      word_eq := rfl
      count := count
      count_eq := rfl
      length_eq := length_filter bank.blocks labels
      admissible := admissible }

end Selection

end Purelib.Polynomial.Dense.Roots.Word

end
