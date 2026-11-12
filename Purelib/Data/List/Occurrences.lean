module

public import Purelib.Data.Vector.Split
public import Purelib.Data.List.Append
import Purelib.Data.Fin
import Purelib.Data.List.Filter
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained occurrence orders and predecessor coordinates

The original ordered word determines both cached finite tables. Each entry
records its number of preceding equal entries and, when present, the exact
preceding occurrence at the immediately lower occurrence order.
-/

public section

namespace Purelib.Data.List

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic

variable {Tag : Type*} [DecidableEq Tag]

/-- Count occurrences of a tag before the supplied finite word position. -/
@[expose] def countBefore (tag : Tag) : List Tag → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | head :: tail, position + 1 =>
      if head = tag then countBefore tag tail position + 1 else countBefore tag tail position

/-- Filtering retains every occurrence of an accepted tag and no occurrence of a rejected tag.

Both counts consume their original finite spines. The Boolean test depends
only on the retained tag, so equal entries select the same filter branch.
-/
theorem countBefore_filter (tag : Tag) (predicate : Tag → Bool) (word : List Tag) :
    countBefore tag (word.filter predicate) (word.filter predicate).length =
      if predicate tag then countBefore tag word word.length else 0 := by
  induction word with
  | nil => cases predicate tag <;> rfl
  | cons head tail previous =>
      rw [Filter.filter_cons]
      cases accepted : predicate head with
      | false =>
          change countBefore tag (tail.filter predicate) (tail.filter predicate).length =
            if predicate tag then
              (if head = tag then countBefore tag tail tail.length + 1 else countBefore tag tail tail.length)
            else 0
          by_cases equal : head = tag
          · cases equal
            rw [accepted]
            exact previous.trans (by rw [accepted]; rfl)
          · rw [if_neg equal]
            exact previous
      | true =>
          change (if head = tag then countBefore tag (tail.filter predicate) (tail.filter predicate).length + 1
              else countBefore tag (tail.filter predicate) (tail.filter predicate).length) =
            if predicate tag then
              (if head = tag then countBefore tag tail tail.length + 1 else countBefore tag tail tail.length)
            else 0
          by_cases equal : head = tag
          · cases equal
            rw [if_pos rfl, accepted, if_pos rfl, previous, accepted, if_pos rfl, if_pos rfl]
          · rw [if_neg equal, if_neg equal]
            exact previous

/-- A prefix ending in the original first list has the same occurrence count after concatenation. -/
theorem countBefore_append_prefix (tag : Tag) (first second : List Tag) (position : Nat)
    (bound : position ≤ first.length) :
    countBefore tag (first ++ second) position = countBefore tag first position := by
  induction first generalizing position with
  | nil =>
      have zero : position = 0 := Nat.eq_zero_of_le_zero bound
      cases zero
      cases second <;> rfl
  | cons head tail previous =>
      cases position with
      | zero => rfl
      | succ position =>
          have cached := previous position (Nat.le_of_succ_le_succ bound)
          change (if head = tag then countBefore tag (tail ++ second) position + 1
            else countBefore tag (tail ++ second) position) = _
          rw [cached]
          rfl

/-- Counting all occurrences in a concatenation adds the two original occurrence counts. -/
theorem countBefore_append (tag : Tag) (first second : List Tag) :
    countBefore tag (first ++ second) (first ++ second).length =
      countBefore tag first first.length + countBefore tag second second.length := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons head tail previous =>
      change (if head = tag then countBefore tag (tail ++ second) (tail ++ second).length + 1
        else countBefore tag (tail ++ second) (tail ++ second).length) =
        (if head = tag then countBefore tag tail tail.length + 1 else countBefore tag tail tail.length) + _
      rw [previous]
      by_cases same : head = tag
      · rw [if_pos same, if_pos same]
        omega0
      · rw [if_neg same, if_neg same]

/-- Replication contains its original count of matching tags and no occurrences of other tags. -/
theorem countBefore_replicate (tag value : Tag) (count : Nat) :
    countBefore tag (List.replicate count value) (List.replicate count value).length =
      if value = tag then count else 0 := by
  induction count with
  | zero =>
      change 0 = if value = tag then 0 else 0
      by_cases same : value = tag
      · rw [if_pos same]
      · rw [if_neg same]
  | succ count previous =>
      rw [List.replicate_succ]
      change (if value = tag then
          countBefore tag (List.replicate count value) (List.replicate count value).length + 1
        else countBefore tag (List.replicate count value) (List.replicate count value).length) = _
      rw [previous]
      by_cases same : value = tag
      · rw [if_pos same, if_pos same, if_pos same]
      · rw [if_neg same, if_neg same, if_neg same]

/-- An injective map preserves every original occurrence prefix count. -/
theorem countBefore_map {Other : Type*} [DecidableEq Other] (function : Tag → Other)
    (injective : ∀ first second, function first = function second → first = second)
    (tag : Tag) (word : List Tag) (position : Nat) :
    countBefore (function tag) (word.map function) position = countBefore tag word position := by
  induction word generalizing position with
  | nil => rfl
  | cons head tail previous =>
      cases position with
      | zero => rfl
      | succ position =>
          change (if function head = function tag then _ else _) = (if head = tag then _ else _)
          by_cases same : head = tag
          · rw [if_pos same, if_pos (congrArg function same), previous]
          · rw [if_neg same, if_neg (fun equal => same (injective head tag equal)), previous]

omit [DecidableEq Tag] in
/-- A map whose original image avoids a tag has no occurrence of that tag in any prefix. -/
theorem countBefore_map_avoiding {Other : Type*} [DecidableEq Other] (function : Tag → Other)
    (target : Other) (avoids : ∀ value, function value ≠ target) (word : List Tag) (position : Nat) :
    countBefore target (word.map function) position = 0 := by
  induction word generalizing position with
  | nil => rfl
  | cons head tail previous =>
      cases position with
      | zero => rfl
      | succ position =>
          change (if function head = target then _ else _) = 0
          rw [if_neg (avoids head)]
          exact previous position

/-- A displayed occurrence has strictly fewer equal predecessors than the complete original word. -/
theorem countBefore_lt_total (word : List Tag) (index : Fin word.length) :
    countBefore (word[index.val]'index.isLt) word index.val <
      countBefore (word[index.val]'index.isLt) word word.length := by
  induction word with
  | nil => exact Fin.elim0 index
  | cons head tail previous =>
      refine Purelib.Data.Fin.cases_induction ?_ (fun index => ?_) index
      · change 0 < if head = head then countBefore head tail tail.length + 1 else _
        rw [if_pos rfl]
        exact Nat.zero_lt_succ _
      · have earlier := previous index
        change (if head = tail[index.val]'index.isLt then _ + 1 else _) <
          (if head = tail[index.val]'index.isLt then _ + 1 else _)
        by_cases same : head = tail[index.val]'index.isLt
        · rw [if_pos same, if_pos same]
          exact Nat.succ_lt_succ earlier
        · rw [if_neg same, if_neg same]
          exact earlier

/-- Every original prefix occurrence count is bounded by its supplied natural position. -/
theorem countBefore_le (tag : Tag) (word : List Tag) (position : Nat) : countBefore tag word position ≤ position := by
  induction word generalizing position with
  | nil => exact Nat.zero_le position
  | cons head tail previous =>
      cases position with
      | zero => exact Nat.le_refl 0
      | succ position =>
          change (if head = tag then countBefore tag tail position + 1 else
            countBefore tag tail position) ≤ position + 1
          by_cases same : head = tag
          · rewrite [if_pos same]
            exact Nat.succ_le_succ (previous position)
          · rewrite [if_neg same]
            exact (previous position).trans (Nat.le_succ position)

/-- Counting a retained tag strictly increases after any original occurrence of that tag. -/
theorem countBefore_lt_of_occurrence (word : List Tag) (tag : Tag) (first second : Fin word.length)
    (occurs : word[first.val]'first.isLt = tag) (before : first.val < second.val) :
    countBefore tag word first.val < countBefore tag word second.val := by
  induction word with
  | nil => exact Fin.elim0 first
  | cons head tail previous =>
      rcases first with ⟨first, firstBound⟩
      rcases second with ⟨second, secondBound⟩
      cases first with
      | zero =>
          cases second with
          | zero => exact False.elim (Nat.lt_irrefl 0 before)
          | succ second =>
              change head = tag at occurs
              change 0 < if head = tag then countBefore tag tail second + 1 else _
              rewrite [if_pos occurs]
              exact Nat.zero_lt_succ _
      | succ first =>
          cases second with
          | zero => exact False.elim (Nat.not_lt_zero _ before)
          | succ second =>
              have firstTail : first < tail.length := Nat.lt_of_succ_lt_succ firstBound
              have secondTail : second < tail.length := Nat.lt_of_succ_lt_succ secondBound
              have old := previous ⟨first, firstTail⟩ ⟨second, secondTail⟩ occurs
                (Nat.lt_of_succ_lt_succ before)
              change (if head = tag then countBefore tag tail first + 1 else _) <
                (if head = tag then countBefore tag tail second + 1 else _)
              by_cases same : head = tag
              · rewrite [if_pos same, if_pos same]
                exact Nat.succ_lt_succ old
              · rewrite [if_neg same, if_neg same]
                exact old

set_option genInjectivity false in
/-- Cached occurrence orders and their bounded original predecessor positions.

The exact original word determines every order. A retained predecessor has
the same original tag and the immediately preceding order, at a strictly
smaller original position. An absent predecessor certifies order zero.
-/
structure Occurrences (word : List Tag) where
  /-- The number of earlier occurrences at each original word coordinate. -/
  orders : Vec Nat word.length
  /-- The retained original coordinate of each preceding occurrence, when present. -/
  predecessors : Vec (Option (Fin word.length)) word.length
  /-- Each stored order reads the actual prefix of the original word. -/
  order_spec : ∀ index, orders index = countBefore (word[index.val]'index.isLt) word index.val
  /-- An entry without a predecessor is its tag's first occurrence. -/
  none_zero : ∀ index, predecessors index = none → orders index = 0
  /-- Every predecessor retains its original position, tag and immediately preceding order. -/
  some_spec : ∀ index previous, predecessors index = some previous →
    previous.val < index.val ∧
      word[previous.val]'previous.isLt = word[index.val]'index.isLt ∧
      orders index = orders previous + 1

constructive_injectivity Occurrences

namespace Occurrences

/-- Every retained occurrence order is at most its original bounded position. -/
theorem order_le {word : List Tag} (retained : Occurrences word) (index : Fin word.length) :
    retained.orders index ≤ index.val := by
  rewrite [retained.order_spec]
  exact countBefore_le _ word index.val

/-- Earlier equal original tags have strictly smaller retained occurrence orders. -/
theorem orders_lt {word : List Tag} (retained : Occurrences word) (first second : Fin word.length)
    (same : word[first.val]'first.isLt = word[second.val]'second.isLt) (before : first.val < second.val) :
    retained.orders first < retained.orders second := by
  rewrite [retained.order_spec first, retained.order_spec second]
  exact (congrArg (fun tag => countBefore tag word first.val) same).trans_lt
    (countBefore_lt_of_occurrence word _ first second same before)

/-- An original tag and its retained occurrence order determine the original bounded index uniquely. -/
theorem eq_of_tag_order_eq {word : List Tag} (retained : Occurrences word) (first second : Fin word.length)
    (same : word[first.val]'first.isLt = word[second.val]'second.isLt)
    (orders : retained.orders first = retained.orders second) : first = second := by
  apply Fin.ext
  by_cases before : first.val < second.val
  · have strict := retained.orders_lt first second same before
    rewrite [orders] at strict
    exact False.elim (Nat.lt_irrefl _ strict)
  · by_cases after : second.val < first.val
    · have strict := retained.orders_lt second first same.symm after
      rewrite [orders] at strict
      exact False.elim (Nat.lt_irrefl _ strict)
    · exact Nat.le_antisymm (Nat.le_of_not_gt after) (Nat.le_of_not_gt before)

/-- Prepend one original tag to an already retained tail occurrence table.

The original tail cache supplies every old order and predecessor. The two
new structural vectors shift those bounded positions exactly once.
-/
@[expose] def prepend (head : Tag) {tail : List Tag} (retained : Occurrences tail) :
    Occurrences (head :: tail) := by
  let orders : Vec Nat (tail.length + 1) := .cons 0 (vectorOfFn fun index : Fin tail.length =>
    if head = tail[index.val]'index.isLt then retained.orders index + 1 else retained.orders index)
  let predecessors : Vec (Option (Fin (tail.length + 1))) (tail.length + 1) :=
    .cons none (vectorOfFn fun index : Fin tail.length =>
      match retained.predecessors index with
      | some previous => some previous.succ
      | none => if head = tail[index.val]'index.isLt then some 0 else none)
  exact
    { orders := orders
      predecessors := predecessors
      order_spec := by
        intro index
        refine Purelib.Data.Fin.cases_induction ?_ (fun index => ?_) index
        · rfl
        · change (vectorOfFn _ : Vec Nat tail.length) index = _
          rw [vectorOfFn_apply]
          change (if head = tail[index.val]'index.isLt then retained.orders index + 1
            else retained.orders index) =
            if head = tail[index.val]'index.isLt then
              countBefore (tail[index.val]'index.isLt) tail index.val + 1
            else countBefore (tail[index.val]'index.isLt) tail index.val
          rw [retained.order_spec index]
      none_zero := by
        intro index
        refine Purelib.Data.Fin.cases_induction ?_ (fun index => ?_) index
        · intro _
          rfl
        · intro absent
          change (vectorOfFn _ : Vec (Option (Fin (tail.length + 1))) tail.length) index = none at absent
          rw [vectorOfFn_apply] at absent
          change (vectorOfFn _ : Vec Nat tail.length) index = 0
          rw [vectorOfFn_apply]
          cases previous : retained.predecessors index with
          | some previousIndex =>
              rw [previous] at absent
              change some previousIndex.succ = none at absent
              cases absent
          | none =>
              rw [previous] at absent
              by_cases same : head = tail[index.val]'index.isLt
              · rw [if_pos same] at absent
                change some (0 : Fin (tail.length + 1)) = none at absent
                cases absent
              · rw [if_neg same]
                exact retained.none_zero index previous
      some_spec := by
        intro index
        refine Purelib.Data.Fin.cases_induction ?_ (fun index => ?_) index
        · intro previous present
          change (none : Option (Fin (tail.length + 1))) = some previous at present
          cases present
        · intro previous present
          change (vectorOfFn _ : Vec (Option (Fin (tail.length + 1))) tail.length) index = some previous at present
          rw [vectorOfFn_apply] at present
          cases old : retained.predecessors index with
          | some oldPrevious =>
              rw [old] at present
              have equal : oldPrevious.succ = previous := Option.some.inj present
              cases equal
              have facts := retained.some_spec index oldPrevious old
              constructor
              · exact Nat.succ_lt_succ facts.1
              constructor
              · exact facts.2.1
              · change (vectorOfFn _ : Vec Nat tail.length) index =
                  (vectorOfFn _ : Vec Nat tail.length) oldPrevious + 1
                rw [vectorOfFn_apply, vectorOfFn_apply]
                by_cases same : head = tail[index.val]'index.isLt
                · have previousSame : head = tail[oldPrevious.val]'oldPrevious.isLt :=
                    same.trans facts.2.1.symm
                  rw [if_pos same, if_pos previousSame, facts.2.2]
                · have previousDifferent : head ≠ tail[oldPrevious.val]'oldPrevious.isLt :=
                    fun equal => same (equal.trans facts.2.1)
                  rw [if_neg same, if_neg previousDifferent]
                  exact facts.2.2
          | none =>
              rw [old] at present
              by_cases same : head = tail[index.val]'index.isLt
              · rw [if_pos same] at present
                have equal : (0 : Fin (tail.length + 1)) = previous := Option.some.inj present
                cases equal
                constructor
                · exact Nat.zero_lt_succ index.val
                constructor
                · exact same
                · change (vectorOfFn _ : Vec Nat tail.length) index = 0 + 1
                  rw [vectorOfFn_apply, if_pos same, retained.none_zero index old]
              · rw [if_neg same] at present
                change (none : Option (Fin (tail.length + 1))) = some previous at present
                cases present }

/-- Retain the original first word's occurrence caches from one prepared concatenation.

Orders use the original structural vector prefix. Each retained predecessor
already lies before its column, so its same natural coordinate is bounded in
the original first word without another occurrence scan.
-/
@[expose] def take (first second : List Tag) (retained : Occurrences (first ++ second)) : Occurrences first := by
  have bound : first.length ≤ (first ++ second).length := by
    rw [Append.length_append]
    exact Nat.le_add_right _ _
  let original (index : Fin first.length) : Fin (first ++ second).length :=
    ⟨index.val, Nat.lt_of_lt_of_le index.isLt bound⟩
  let orders := Vector.Split.take bound retained.orders
  let predecessors : Vec (Option (Fin first.length)) first.length := vectorOfFn fun index =>
    match previous : retained.predecessors (original index) with
    | none => none
    | some prior => some ⟨prior.val, by
        have facts := retained.some_spec (original index) prior previous
        exact Nat.lt_trans facts.1 index.isLt⟩
  exact
    { orders := orders
      predecessors := predecessors
      order_spec := by
        intro index
        dsimp only [orders]
        rw [Vector.Split.take_apply, retained.order_spec,
          Append.getElem_append_left first second index.val index.isLt]
        exact countBefore_append_prefix _ first second index.val (Nat.le_of_lt index.isLt)
      none_zero := by
        intro index absent
        dsimp only [predecessors] at absent
        rw [vectorOfFn_apply] at absent
        split at absent
        next previous =>
          dsimp only [orders]
          rw [Vector.Split.take_apply]
          exact retained.none_zero (original index) previous
        next prior previous =>
          change some _ = none at absent
          cases absent
      some_spec := by
        intro index prior present
        dsimp only [predecessors] at present
        rw [vectorOfFn_apply] at present
        split at present
        next previous =>
          change none = some prior at present
          cases present
        next oldPrior previous =>
          have facts := retained.some_spec (original index) oldPrior previous
          have priorBound : oldPrior.val < first.length := Nat.lt_trans facts.1 index.isLt
          have equal : (⟨oldPrior.val, priorBound⟩ : Fin first.length) = prior := Option.some.inj present
          have coordinates := congrArg Fin.val equal
          have originalPrior : original prior = oldPrior := Fin.ext coordinates.symm
          constructor
          · exact coordinates ▸ facts.1
          constructor
          · have tags := facts.2.1
            rw [← originalPrior,
              Append.getElem_append_left first second prior.val prior.isLt,
              Append.getElem_append_left first second index.val index.isLt] at tags
            exact tags
          · dsimp only [orders]
            rw [Vector.Split.take_apply, Vector.Split.take_apply]
            exact facts.2.2.trans
              (congrArg (fun value => retained.orders value + 1) originalPrior).symm }

/-- The original prefix order is the exact retained order at the same concatenated coordinate. -/
theorem take_order (first second : List Tag) (retained : Occurrences (first ++ second))
    (index : Fin first.length) (bound : index.val < (first ++ second).length) :
    (take first second retained).orders index = retained.orders ⟨index.val, bound⟩ := by
  have fullBound : first.length ≤ (first ++ second).length := by
    rw [Append.length_append]
    exact Nat.le_add_right _ _
  exact Vector.Split.take_apply fullBound retained.orders index

/-- Prepare both occurrence tables once by structural recursion on the original word.

Each successor step consumes the same retained tail through prepend; it does
not run a second occurrence scan.
-/
@[expose] def prepare : (word : List Tag) → Occurrences word
  | [] =>
      { orders := .nil
        predecessors := .nil
        order_spec := fun index => Fin.elim0 index
        none_zero := fun index => Fin.elim0 index
        some_spec := fun index => Fin.elim0 index }
  | head :: tail => prepend head (prepare tail)

/-- Prepending assigns order zero to the new original first coordinate. -/
theorem prepend_order_zero (head : Tag) {tail : List Tag} (retained : Occurrences tail) :
    (prepend head retained).orders 0 = 0 := rfl

/-- Prepending shifts precisely the occurrence orders of the same original tag. -/
theorem prepend_order_succ (head : Tag) {tail : List Tag} (retained : Occurrences tail)
    (index : Fin tail.length) :
    (prepend head retained).orders index.succ =
      if head = tail[index.val]'index.isLt then retained.orders index + 1 else retained.orders index :=
  vectorOfFn_apply _ _

/-- The prepended first coordinate has no original predecessor. -/
theorem prepend_predecessor_zero (head : Tag) {tail : List Tag} (retained : Occurrences tail) :
    (prepend head retained).predecessors 0 = none := rfl

/-- Prepending transports each same retained predecessor, or supplies the new first coordinate. -/
theorem prepend_predecessor_succ (head : Tag) {tail : List Tag} (retained : Occurrences tail)
    (index : Fin tail.length) :
    (prepend head retained).predecessors index.succ =
      match retained.predecessors index with
      | some previous => some previous.succ
      | none => if head = tail[index.val]'index.isLt then some 0 else none :=
  vectorOfFn_apply _ _

end Occurrences
end Purelib.Data.List
