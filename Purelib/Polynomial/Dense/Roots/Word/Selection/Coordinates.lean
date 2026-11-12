module

public import Purelib.Polynomial.Dense.Roots.Word.Selection
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Fin
import Purelib.Data.List.Filter
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coordinates of the original retained word selection

The position map reads the same complete word and its Boolean labels. Its
zero extension and restriction preserve every selected original occurrence,
including its generalized order. No root bank or selection is reconstructed.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Word.Selection

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {Tag : Type*}

/-- Locate a filtered occurrence in its original finite word. -/
private def positionNat (predicate : Tag → Bool) : List Tag → Nat → Nat
  | [], _ => 0
  | head :: tail, index =>
      if predicate head then
        match index with
        | 0 => 0
        | index + 1 => positionNat predicate tail index + 1
      else positionNat predicate tail index + 1

/-- A retained filtered occurrence has an original bounded position. -/
private theorem positionNat_lt (predicate : Tag → Bool) (word : List Tag) (index : Nat)
    (bound : index < (word.filter predicate).length) : positionNat predicate word index < word.length := by
  induction word generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons head tail previous =>
      rw [Filter.filter_cons] at bound
      cases accepted : predicate head with
      | false =>
          rw [accepted, if_neg Bool.noConfusion] at bound
          change index < (tail.filter predicate).length at bound
          change (if predicate head then _ else _) < _
          rw [accepted, if_neg Bool.noConfusion]
          exact Nat.succ_lt_succ (previous index bound)
      | true =>
          rw [accepted, if_pos rfl] at bound
          cases index with
          | zero =>
              change (if predicate head then _ else _) < _
              rw [accepted, if_pos rfl]
              exact Nat.zero_lt_succ _
          | succ index =>
              change index + 1 < (tail.filter predicate).length + 1 at bound
              change (if predicate head then _ else _) < _
              rw [accepted, if_pos rfl]
              exact Nat.succ_lt_succ (previous index (Nat.lt_of_succ_lt_succ bound))

/-- The original position carries the same retained tag. -/
private theorem positionNat_tag (predicate : Tag → Bool) (word : List Tag) (index : Nat)
    (bound : index < (word.filter predicate).length) :
    word[positionNat predicate word index]'(positionNat_lt predicate word index bound) =
      (word.filter predicate)[index]'bound := by
  induction word generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons head tail previous =>
      cases accepted : predicate head with
      | false =>
          have same := Filter.filter_cons_of_neg (predicate := predicate) (head := head) (tail := tail)
            (by rw [accepted]; intro impossible; nomatch impossible)
          have tailBound : index < (tail.filter predicate).length := (congrArg List.length same) ▸ bound
          have position : positionNat predicate (head :: tail) index = positionNat predicate tail index + 1 := by
            change (if predicate head then _ else _) = _
            rw [accepted, if_neg Bool.noConfusion]
          simp only [position, same, -eq_self, -iff_self]
          exact previous index tailBound
      | true =>
          have same := Filter.filter_cons_of_pos (predicate := predicate) (head := head) (tail := tail) accepted
          cases index with
          | zero =>
              have position : positionNat predicate (head :: tail) 0 = 0 := by
                change (if predicate head then _ else _) = _
                rw [accepted, if_pos rfl]
              simp only [position, same, -eq_self, -iff_self]
              rfl
          | succ index =>
              have tailBound : index < (tail.filter predicate).length :=
                by
                  have atHead : Nat.succ index < (head :: tail.filter predicate).length :=
                    Eq.mp (congrArg (fun length => Nat.succ index < length) (congrArg List.length same)) bound
                  exact Nat.lt_of_succ_lt_succ atHead
              have position : positionNat predicate (head :: tail) (index + 1) =
                  positionNat predicate tail index + 1 := by
                change (if predicate head then _ else _) = _
                rw [accepted, if_pos rfl]
              simp only [position, same, -eq_self, -iff_self]
              exact previous index tailBound

/-- The original position of a selected occurrence retains a true source label. -/
private theorem positionNat_accepted (predicate : Tag → Bool) (word : List Tag) (index : Nat)
    (bound : index < (word.filter predicate).length) :
    predicate (word[positionNat predicate word index]'(positionNat_lt predicate word index bound)) = true := by
  rw [positionNat_tag predicate word index bound]
  exact (Filter.mem_filter.mp (List.getElem_mem bound)).2

/-- Counting an accepted fixed tag before a selected position preserves its same original prefix count. -/
private theorem positionNat_count [DecidableEq Tag] (predicate : Tag → Bool) (tag : Tag)
    (tagAccepted : predicate tag = true) (word : List Tag) (index : Nat)
    (bound : index < (word.filter predicate).length) :
    countBefore tag word (positionNat predicate word index) = countBefore tag (word.filter predicate) index := by
  induction word generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons head tail previous =>
      cases accepted : predicate head with
      | false =>
          have same := Filter.filter_cons_of_neg (predicate := predicate) (head := head) (tail := tail)
            (by rw [accepted]; intro impossible; nomatch impossible)
          have tailBound : index < (tail.filter predicate).length := (congrArg List.length same) ▸ bound
          have other : head ≠ tag := by
            intro equal
            exact Bool.noConfusion (accepted.symm.trans ((congrArg predicate equal).trans tagAccepted))
          have position : positionNat predicate (head :: tail) index = positionNat predicate tail index + 1 := by
            change (if predicate head then _ else _) = _
            rw [accepted, if_neg Bool.noConfusion]
          rw [same, position, countBefore, if_neg other]
          exact previous index tailBound
      | true =>
          have same := Filter.filter_cons_of_pos (predicate := predicate) (head := head) (tail := tail) accepted
          cases index with
          | zero =>
              have position : positionNat predicate (head :: tail) 0 = 0 := by
                change (if predicate head then _ else _) = _
                rw [accepted, if_pos rfl]
              rw [same, position]
              rfl
          | succ index =>
              have tailBound : index < (tail.filter predicate).length := by
                have atHead : Nat.succ index < (head :: tail.filter predicate).length :=
                  Eq.mp (congrArg (fun length => Nat.succ index < length) (congrArg List.length same)) bound
                exact Nat.lt_of_succ_lt_succ atHead
              have position : positionNat predicate (head :: tail) (index + 1) =
                  positionNat predicate tail index + 1 := by
                change (if predicate head then _ else _) = _
                rw [accepted, if_pos rfl]
              rw [same, position]
              change (if head = tag then countBefore tag tail (positionNat predicate tail index) + 1 else
                  countBefore tag tail (positionNat predicate tail index)) =
                (if head = tag then countBefore tag (tail.filter predicate) index + 1 else
                  countBefore tag (tail.filter predicate) index)
              rw [previous index tailBound]

/-- The filtered position map preserves the same original occurrence order. -/
private theorem positionNat_order [DecidableEq Tag] (predicate : Tag → Bool) (word : List Tag) (index : Nat)
    (bound : index < (word.filter predicate).length) :
    countBefore ((word.filter predicate)[index]'bound) word (positionNat predicate word index) =
      countBefore ((word.filter predicate)[index]'bound) (word.filter predicate) index :=
  positionNat_count predicate _ (Filter.mem_filter.mp (List.getElem_mem bound)).2 word index bound

/-- Every accepted original position is the image of a bounded selected position. -/
private theorem positionNat_complete (predicate : Tag → Bool) (word : List Tag) (index : Fin word.length)
    (accepted : predicate (word[index.val]'index.isLt) = true) :
    ∃ selected : Nat, selected < (word.filter predicate).length ∧ positionNat predicate word selected = index.val := by
  induction word with
  | nil => exact Fin.elim0 index
  | cons head tail previous =>
      revert accepted
      cases chosen : predicate head with
      | false =>
          have same := Filter.filter_cons_of_neg (predicate := predicate) (head := head) (tail := tail)
            (by rw [chosen]; intro impossible; nomatch impossible)
          refine Purelib.Data.Fin.cases_induction ?_ (fun index accepted => ?_) index
          · intro accepted
            exact False.elim (Bool.noConfusion (chosen.symm.trans accepted))
          · rcases previous index accepted with ⟨selected, bound, position⟩
            refine ⟨selected, (congrArg List.length same).symm ▸ bound, ?_⟩
            change (if predicate head then _ else _) = _
            rw [chosen, if_neg Bool.noConfusion]
            exact congrArg Nat.succ position
      | true =>
          have same := Filter.filter_cons_of_pos (predicate := predicate) (head := head) (tail := tail) chosen
          refine Purelib.Data.Fin.cases_induction ?_ (fun index accepted => ?_) index
          · intro _
            refine ⟨0, (congrArg List.length same).symm ▸ Nat.zero_lt_succ _, ?_⟩
            change (if predicate head then _ else _) = _
            rw [chosen, if_pos rfl]
          · rcases previous index accepted with ⟨selected, bound, position⟩
            refine ⟨selected + 1, (congrArg List.length same).symm ▸ Nat.succ_lt_succ bound, ?_⟩
            change (if predicate head then _ else _) = _
            rw [chosen, if_pos rfl]
            exact congrArg Nat.succ position

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}

set_option genInjectivity false in
/-- The cached original positions of every occurrence in the same retained selected word.

Both words and their labels remain owned by the original selection. Tags,
generalized occurrence orders and complete coverage of true labels certify
the single retained position vector, without another root or word producer.
-/
structure Coordinates (selection : Selection bank) where
  /-- Each selected original occurrence retains its position in the same full word. -/
  positions : Vec (Fin selection.fullWord.length) selection.word.length
  /-- Every stored position preserves its original root-block tag. -/
  tags : ∀ index, selection.fullWord[(positions index).val]'(positions index).isLt =
    selection.word[index.val]'index.isLt
  /-- Every stored position preserves the same original generalized occurrence order. -/
  orders : ∀ index,
    countBefore (selection.word[index.val]'index.isLt) selection.fullWord (positions index).val =
      countBefore (selection.word[index.val]'index.isLt) selection.word index.val
  /-- Every originally accepted full-word coordinate occurs in this same position vector. -/
  complete : ∀ index : Fin selection.fullWord.length,
    selection.labels (selection.fullWord[index.val]'index.isLt) = true →
      ∃ selected, positions selected = index

constructive_injectivity Coordinates

namespace Coordinates

variable {selection : Selection bank}

/-- Equal original list owners retain the same bounded scalar entry at its unchanged natural index. -/
private theorem get_transport {Item : Type*} (first second : List Item) (same : first = second)
    (index : Nat) (firstBound : index < first.length) (secondBound : index < second.length) :
    first[index]'firstBound = second[index]'secondBound := by
  cases same
  rfl

/-- Materialize one position vector from the same retained full and selected words.

The vector dimension reads the already retained selected word. Its filter
equality is used only to transport proof bounds; the executable constructor
neither expands the original roots nor filters the complete word again.
-/
def prepare (selection : Selection bank) : Coordinates selection := by
  let filteredBound (index : Fin selection.word.length) :
      index.val < (selection.fullWord.filter (fun tag => selection.labels tag)).length :=
    Eq.mp (congrArg (fun length => index.val < length) (congrArg List.length selection.word_eq)) index.isLt
  let positions := vectorOfFn fun index : Fin selection.word.length =>
    (⟨positionNat (fun tag => selection.labels tag) selection.fullWord index.val,
      positionNat_lt (fun tag => selection.labels tag) selection.fullWord index.val (filteredBound index)⟩ :
        Fin selection.fullWord.length)
  exact
    { positions := positions
      tags := fun index => by
        rw [vectorOfFn_apply]
        exact (positionNat_tag (fun tag => selection.labels tag) selection.fullWord index.val
          (filteredBound index)).trans (get_transport selection.word _ selection.word_eq index.val index.isLt
            (filteredBound index)).symm
      orders := fun index => by
        rw [vectorOfFn_apply]
        exact (positionNat_count (fun tag => selection.labels tag) (selection.word[index.val]'index.isLt)
          (selection.accepted index) selection.fullWord index.val (filteredBound index)).trans
            (congrArg (fun word => countBefore (selection.word[index.val]'index.isLt) word index.val)
              selection.word_eq.symm)
      complete := fun index accepted => by
        rcases positionNat_complete (fun tag => selection.labels tag) selection.fullWord index accepted with
          ⟨selected, bound, same⟩
        have storedBound : selected < selection.word.length :=
          Eq.mpr (congrArg (fun length => selected < length) (congrArg List.length selection.word_eq)) bound
        refine ⟨⟨selected, storedBound⟩, ?_⟩
        rw [vectorOfFn_apply]
        exact Fin.ext same }

/-- The same original tag and occurrence order determine a finite word position uniquely. -/
private theorem index_unique (word : List (Fin bank.blocks.length)) (first second : Fin word.length)
    (tags : word[first.val]'first.isLt = word[second.val]'second.isLt)
    (orders : countBefore (word[first.val]'first.isLt) word first.val =
      countBefore (word[second.val]'second.isLt) word second.val) : first = second := by
  let original := Occurrences.prepare word
  exact original.eq_of_tag_order_eq first second tags ((original.order_spec first).trans
    (orders.trans (original.order_spec second).symm))

/-- The cached coordinate inclusion is injective on the same original selected occurrences. -/
theorem injective (retained : Coordinates selection) : Function.Injective retained.positions := by
  intro first second same
  have tags := (retained.tags first).symm.trans
    ((congrArg (fun index : Fin selection.fullWord.length => selection.fullWord[index.val]'index.isLt) same).trans
      (retained.tags second))
  apply index_unique selection.word first second tags
  exact (retained.orders first).symm.trans ((congrArg₂
    (fun tag position => countBefore tag selection.fullWord position) tags (congrArg Fin.val same)).trans
      (retained.orders second))

/-- Every position in the retained inclusion carries a true original label. -/
theorem accepted (retained : Coordinates selection) (index : Fin selection.word.length) :
    selection.labels (selection.fullWord[(retained.positions index).val]'(retained.positions index).isLt) = true :=
  (congrArg selection.labels (retained.tags index)).trans (selection.accepted index)

/-- The same cached full and selected occurrence tables agree at every original included position. -/
theorem occurrence_order (retained : Coordinates selection) (full : Occurrences selection.fullWord)
    (selected : Occurrences selection.word) (index : Fin selection.word.length) :
    full.orders (retained.positions index) = selected.orders index :=
  (full.order_spec _).trans ((congrArg
    (fun tag => countBefore tag selection.fullWord (retained.positions index).val) (retained.tags index)).trans
      ((retained.orders index).trans (selected.order_spec index).symm))

/-- Any two certified position caches of the same original selection have the same complete value. -/
theorem unique (first second : Coordinates selection) : first = second := by
  have same : first.positions = second.positions := by
    apply vector_ext
    intro index
    apply index_unique selection.fullWord
    · exact (first.tags index).trans (second.tags index).symm
    · exact (congrArg (fun tag => countBefore tag selection.fullWord (first.positions index).val)
        (first.tags index)).trans ((first.orders index).trans ((second.orders index).symm.trans
          (congrArg (fun tag => countBefore tag selection.fullWord (second.positions index).val)
            (second.tags index).symm)))
  cases first
  cases second
  cases same
  rfl

/-- The complete retained position cache restores its canonical same-word preparation. -/
theorem restore (retained : Coordinates selection) : retained = prepare selection := retained.unique (prepare selection)

/-- Restrict an original complete coefficient vector to its same cached selected positions. -/
def restrict (retained : Coordinates selection) (values : Vec K selection.fullWord.length) :
    Vec K selection.word.length := vectorOfFn fun index => values (retained.positions index)

/-- The actual restricted entry reads its same original full-word coefficient. -/
theorem restrict_at (retained : Coordinates selection) (values : Vec K selection.fullWord.length)
    (index : Fin selection.word.length) : retained.restrict values index = values (retained.positions index) :=
  vectorOfFn_apply _ _

/-- Extend selected coefficients by zero at every other original full-word coordinate.

The same cached positions determine the finite inclusion. Every selected
coefficient is retained exactly once; no root, label filter or occurrence
order is recomputed by the operation.
-/
def extend (retained : Coordinates selection) (values : Vec K selection.word.length) :
    Vec K selection.fullWord.length := vectorOfFn fun original =>
      sumFin fun selected => if retained.positions selected = original then values selected else 0

/-- Extension at a cached selected position returns its same original coefficient. -/
theorem extend_at (retained : Coordinates selection) (values : Vec K selection.word.length)
    (index : Fin selection.word.length) : retained.extend values (retained.positions index) = values index := by
  rw [extend, vectorOfFn_apply]
  have terms : sumFin (fun selected => if retained.positions selected = retained.positions index then
      values selected else 0) = sumFin (fun selected => if selected = index then values selected else 0) := by
    apply sumFin_congr
    intro selected
    by_cases same : selected = index
    · cases same
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg same, if_neg (fun equal => same (retained.injective equal))]
  exact terms.trans (sumFin_ite_eq index values)

/-- Extension vanishes at every originally rejected full-word coordinate. -/
theorem extend_rejected (retained : Coordinates selection) (values : Vec K selection.word.length)
    (index : Fin selection.fullWord.length)
    (rejected : selection.labels (selection.fullWord[index.val]'index.isLt) = false) :
    retained.extend values index = 0 := by
  rw [extend, vectorOfFn_apply]
  have terms : sumFin (fun selected => if retained.positions selected = index then values selected else 0) =
      sumFin (fun _ : Fin selection.word.length => (0 : K)) := by
    apply sumFin_congr
    intro selected
    apply if_neg
    intro same
    have accepted := retained.accepted selected
    rw [same, rejected] at accepted
    exact Bool.noConfusion accepted
  exact terms.trans sumFin_zero

/-- Restricting the same zero extension recovers the complete original selected coefficient vector. -/
theorem restrict_extend (retained : Coordinates selection) (values : Vec K selection.word.length) :
    retained.restrict (retained.extend values) = values := by
  apply vector_ext
  intro index
  rw [retained.restrict_at]
  exact retained.extend_at values index

/-- Zero extension after restriction is exactly the original full-word label mask. -/
theorem extend_restrict (retained : Coordinates selection) (values : Vec K selection.fullWord.length) :
    retained.extend (retained.restrict values) = vectorOfFn (fun index =>
      if selection.labels (selection.fullWord[index.val]'index.isLt) then values index else 0) := by
  apply vector_ext
  intro index
  rw [vectorOfFn_apply]
  cases chosen : selection.labels (selection.fullWord[index.val]'index.isLt) with
  | false =>
      rw [if_neg Bool.noConfusion]
      exact retained.extend_rejected _ index chosen
  | true =>
      rw [if_pos rfl]
      rcases retained.complete index chosen with ⟨selected, same⟩
      exact (congrArg (fun position => retained.extend (retained.restrict values) position) same.symm).trans
        ((retained.extend_at _ selected).trans ((retained.restrict_at values selected).trans (congrArg values same)))

/-- The original full coefficient vector belongs to the selected inclusion exactly when its rejected entries vanish.

Vanishing here is equality in the original finite coefficient ring. It is
not inferred from any possibly noninjective Gaussian reading.
-/
theorem support_iff (retained : Coordinates selection) (values : Vec K selection.fullWord.length) :
    retained.extend (retained.restrict values) = values ↔
      ∀ index : Fin selection.fullWord.length,
        selection.labels (selection.fullWord[index.val]'index.isLt) = false → values index = 0 := by
  constructor
  · intro same index rejected
    exact (congrArg (fun vector : Vec K selection.fullWord.length => vector index) same).symm.trans
      (retained.extend_rejected _ index rejected)
  · intro supported
    rw [retained.extend_restrict]
    apply vector_ext
    intro index
    rw [vectorOfFn_apply]
    cases chosen : selection.labels (selection.fullWord[index.val]'index.isLt) with
    | false => rw [if_neg Bool.noConfusion]; exact (supported index chosen).symm
    | true => rw [if_pos rfl]

/-- Zero extension preserves the actual finite weighted sum at its same original cached coordinates. -/
theorem sum_extend (retained : Coordinates selection) (weights : Vec K selection.fullWord.length)
    (values : Vec K selection.word.length) :
    sumFin (fun original => weights original * retained.extend values original) =
      sumFin (fun selected => weights (retained.positions selected) * values selected) := by
  have distribute : sumFin (fun original => weights original * retained.extend values original) =
      sumFin (fun original => sumFin (fun selected =>
        if retained.positions selected = original then weights original * values selected else 0)) := by
    apply sumFin_congr
    intro original
    rw [extend, vectorOfFn_apply, ← sumFin_mul_left]
    apply sumFin_congr
    intro selected
    by_cases same : retained.positions selected = original
    · rw [if_pos same, if_pos same]
    · rw [if_neg same, if_neg same, mul_zero]
  rw [distribute, sumFin_swap]
  apply sumFin_congr
  intro selected
  have terms : sumFin (fun original => if retained.positions selected = original then
      weights original * values selected else 0) = sumFin (fun original =>
        if original = retained.positions selected then weights original * values selected else 0) := by
    apply sumFin_congr
    intro original
    by_cases same : original = retained.positions selected
    · rw [if_pos same, if_pos same.symm]
    · rw [if_neg same, if_neg (fun equal => same equal.symm)]
  exact terms.trans (sumFin_ite_eq (retained.positions selected) _)

end Coordinates
end Purelib.Polynomial.Dense.Roots.Word.Selection

end
