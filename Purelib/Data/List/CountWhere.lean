module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Filter
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.List.Fold
import Mathlib.Algebra.Group.Nat.Defs

/-! Boolean occurrence counts and their structural finite-list certificates. -/

namespace Purelib.Data.List.CountWhere

open Purelib.Data.List

/-- Count accepted occurrences by taking the length of a finite Boolean filter. -/
@[expose] public def listCountWhere {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) : Nat :=
  (values.filter predicate).length

/-- Boolean filtered counts add across concatenation.

The original two spines retain their order and multiplicity. Filtering each
spine separately therefore gives the same accepted occurrence count. -/
public theorem listCountWhere_append {Alpha : Type*}
    (left right : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere (left ++ right) predicate =
      listCountWhere left predicate + listCountWhere right predicate := by
  unfold listCountWhere
  rw [Filter.filter_append, Append.length_append]

/-- Counting a mapped list equals counting the source with the composed Boolean
predicate.

Each retained source occurrence contributes exactly when its mapped value is
accepted. Repeated values contribute once for each source occurrence. -/
public theorem listCountWhere_map {Alpha Beta : Type*}
    (values : List Alpha) (function : Alpha → Beta)
    (predicate : Beta → Bool) :
    listCountWhere (values.map function) predicate =
      listCountWhere values (fun value => predicate (function value)) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.map_cons, Filter.filter_cons, Filter.filter_cons]
      cases accepted : predicate (function head) with
      | false =>
          change (List.filter predicate (List.map function tail)).length =
            (List.filter (fun value => predicate (function value)) tail).length
          exact inductionHypothesis
      | true =>
          change Nat.succ
              (List.filter predicate (List.map function tail)).length =
            Nat.succ
              (List.filter (fun value => predicate (function value)) tail).length
          exact congrArg Nat.succ inductionHypothesis

/-- Boolean predicates equal on all displayed entries have equal filtered counts.

Only members of the retained list require equality of the Boolean tests. Their
accepted occurrence counts agree by comparing each head and the unchanged tail. -/
public theorem listCountWhere_congr {Alpha : Type*}
    (values : List Alpha) (left right : Alpha → Bool)
    (pointwise : ∀ value ∈ values, left value = right value) :
    listCountWhere values left = listCountWhere values right := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [Filter.filter_cons, Filter.filter_cons,
        pointwise head List.mem_cons_self]
      cases accepted : right head with
      | false =>
          exact inductionHypothesis (fun value member =>
            pointwise value (List.mem_cons_of_mem head member))
      | true =>
          exact congrArg Nat.succ
            (inductionHypothesis (fun value member =>
              pointwise value (List.mem_cons_of_mem head member)))

/-- A predicate rejecting every displayed entry has filtered count zero.

The rejection certificate covers every retained source occurrence, so neither
the head nor any remaining entry contributes to the filtered length. -/
public theorem listCountWhere_eq_zero_of_reject {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool)
    (reject : ∀ value ∈ values, predicate value = false) :
    listCountWhere values predicate = 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [Filter.filter_cons, reject head List.mem_cons_self]
      exact inductionHypothesis (fun value member =>
        reject value (List.mem_cons_of_mem head member))

/-- The accepted and rejected occurrence counts sum to the original list length.

A Boolean test and its negation select exactly one side for each displayed
occurrence. Their counts therefore partition the original retained length. -/
public theorem listCountWhere_add_complement {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere values predicate +
      listCountWhere values (fun value => !predicate value) = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [Filter.filter_cons, Filter.filter_cons]
      cases accepted : predicate head with
      | false =>
          rw [Bool.not_false]
          change (tail.filter predicate).length +
            Nat.succ (tail.filter fun value => !predicate value).length =
              Nat.succ tail.length
          rw [Nat.add_succ, inductionHypothesis]
      | true =>
          rw [Bool.not_true]
          change Nat.succ (tail.filter predicate).length +
            (tail.filter fun value => !predicate value).length =
              Nat.succ tail.length
          rw [Nat.succ_add, inductionHypothesis]

/-- Predicates complementary on the displayed list have counts summing to its length.

The supplied pointwise equality identifies the second test with the Boolean
negation of the first on every retained entry, including repeated occurrences. -/
public theorem listCountWhere_add_complementary {Alpha : Type*}
    (values : List Alpha) (accepted rejected : Alpha → Bool)
    (complementary : ∀ value ∈ values, (!accepted value) = rejected value) :
    listCountWhere values accepted + listCountWhere values rejected =
      values.length := by
  have equal := listCountWhere_congr values
    (fun value => !accepted value) rejected complementary
  rw [← equal]
  exact listCountWhere_add_complement values accepted

/-- A finite Boolean filtered count equals the sum of its zero-or-one indicators.

The ordered finite fold contributes one for an accepted occurrence and zero
for a rejected occurrence. Its natural sum equals the filtered list length. -/
public theorem listCountWhere_eq_foldr_indicators {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere values predicate =
      (values.map fun value => if predicate value then 1 else 0).foldr
        Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [Filter.filter_cons, List.map_cons, List.foldr_cons]
      cases accepted : predicate head with
      | false =>
          rw [if_neg (by decide : ¬ (false = true)),
            if_neg (by decide : ¬ (false = true))]
          exact inductionHypothesis.trans
            (Nat.zero_add _).symm
      | true =>
          rw [if_pos rfl, if_pos rfl, List.length_cons]
          calc
            (tail.filter predicate).length + 1 =
                1 + (tail.filter predicate).length := Nat.add_comm _ _
            _ = 1 +
                ((tail.map fun value =>
                  if predicate value then 1 else 0).foldr Nat.add 0) :=
              congrArg (Nat.add 1) inductionHypothesis

/-- A Boolean filtered count adds the head's indicator to the tail count.

The retained head contributes one exactly when its test is true. The tail
uses the original predicate without changing its occurrence order. -/
private theorem listCountWhere_cons {Alpha : Type*}
    (head : Alpha) (tail : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere (head :: tail) predicate =
      (if predicate head then 1 else 0) + listCountWhere tail predicate := by
  unfold listCountWhere
  rw [Filter.filter_cons]
  cases predicate head with
  | false =>
      rw [if_neg (by decide : ¬ (false = true)),
        if_neg (by decide : ¬ (false = true)), Nat.zero_add]
  | true =>
      rw [if_pos rfl, if_pos rfl, List.length_cons]
      exact Nat.add_comm _ _

/-- Interchange the two finite counting orders for a Boolean predicate on a Cartesian
list.

For two displayed lists, summing accepted right entries for each left entry equals
summing accepted left entries for each right entry, including multiplicities on both
sides. -/
public theorem listCountWhere_sum_swap {Alpha Beta : Type*}
    (left : List Alpha) (right : List Beta)
    (predicate : Alpha → Beta → Bool) :
    (left.map fun leftValue =>
        listCountWhere right (predicate leftValue)).foldr Nat.add 0 =
      (right.map fun rightValue =>
        listCountWhere left (fun leftValue =>
          predicate leftValue rightValue)).foldr Nat.add 0 := by
  induction left with
  | nil =>
      rw [List.map_nil, List.foldr_nil]
      change 0 = (right.map fun _ => 0).foldr Nat.add 0
      exact (Fold.foldr_add_map_zero right).symm
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.foldr_cons]
      calc
        listCountWhere right (predicate head) +
            (tail.map fun leftValue =>
              listCountWhere right (predicate leftValue)).foldr Nat.add 0 =
          (right.map fun rightValue =>
              (if predicate head rightValue then 1 else 0)).foldr Nat.add 0 +
            (right.map fun rightValue =>
              listCountWhere tail (fun leftValue =>
                predicate leftValue rightValue)).foldr Nat.add 0 := by
          rw [← listCountWhere_eq_foldr_indicators right (predicate head),
            inductionHypothesis]
        _ = (right.map fun rightValue =>
            (if predicate head rightValue then 1 else 0) +
              listCountWhere tail (fun leftValue =>
                predicate leftValue rightValue)).foldr Nat.add 0 :=
          (Fold.foldr_add_map_pointwise_add right
            (fun rightValue => if predicate head rightValue then 1 else 0)
            (fun rightValue => listCountWhere tail (fun leftValue =>
              predicate leftValue rightValue))).symm
        _ = (right.map fun rightValue =>
            listCountWhere (head :: tail) (fun leftValue =>
              predicate leftValue rightValue)).foldr Nat.add 0 := by
          apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
          apply Map.map_congr_left
          intro rightValue _
          exact (listCountWhere_cons head tail (fun leftValue =>
            predicate leftValue rightValue)).symm

/-- A target occurring in a duplicate-free list is selected exactly once by equality.

The explicit decidable-equality argument drives the Boolean predicate; retained
membership supplies existence and Nodup excludes every second occurrence. -/
public theorem listCountWhere_eq_one_of_eq_target {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (values : List Alpha)
    (valuesNodup : values.Nodup) (target : Alpha) (targetMember : target ∈ values) :
    (letI : DecidableEq Alpha := eqDecidable
     listCountWhere values fun value => decide (value = target)) = 1 := by
  letI : DecidableEq Alpha := eqDecidable
  induction values with
  | nil => nomatch targetMember
  | cons head tail inductionHypothesis =>
      cases eqDecidable head target with
      | isTrue equal =>
          have targetNotInTail : target ∉ tail := by
            intro member
            apply (List.pairwise_cons.mp valuesNodup).1 target member
            exact equal
          rw [listCountWhere_cons]
          rw [decide_eq_true equal, if_pos rfl]
          have tailZero := listCountWhere_eq_zero_of_reject tail
            (fun value => decide (value = target)) (by
              intro value member
              apply decide_eq_false
              intro valueEqual
              exact targetNotInTail (valueEqual ▸ member))
          rw [tailZero]
      | isFalse different =>
          rw [listCountWhere_cons]
          rw [decide_eq_false different]
          rw [if_neg (by intro impossible; nomatch impossible), Nat.zero_add]
          apply inductionHypothesis (List.pairwise_cons.mp valuesNodup).2
          cases targetMember with
          | head => exact False.elim (different rfl)
          | tail _ tailMember => exact tailMember

/-- A filtered count over a finite flat-map equals the sum of filtered counts in each
fiber.

Each displayed source occurrence contributes its original list-valued fiber.
The natural fold adds the accepted counts of those fibers in their source order. -/
public theorem listCountWhere_flatMap {Alpha Beta : Type*}
    (values : List Alpha) (fiber : Alpha → List Beta)
    (predicate : Beta → Bool) :
    listCountWhere (values.flatMap fiber) predicate =
      (values.map fun value =>
        listCountWhere (fiber value) predicate).foldr Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [Flatten.flatMap_cons, listCountWhere_append,
        inductionHypothesis, List.map_cons, List.foldr_cons]
      rfl

/-- The length of a finite filterMap equals the number of inputs returning some value.

The original option-valued operation contributes one output for each successful
source occurrence and no output for a none result, including repeated outputs. -/
public theorem length_filterMap_eq_count_isSome
    {Alpha Beta : Type*} (values : List Alpha) (function : Alpha → Option Beta) :
    (values.filterMap function).length =
      listCountWhere values (fun value => (function value).isSome) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases selected : function head with
      | none =>
          have rejected : (function head).isSome = false :=
            congrArg Option.isSome selected
          rw [FilterMap.filterMap_cons_none selected]
          unfold listCountWhere at inductionHypothesis ⊢
          rw [Filter.filter_cons]
          rw [rejected]
          change (tail.filterMap function).length =
            (tail.filter fun value => (function value).isSome).length
          exact inductionHypothesis
      | some result =>
          have accepted : (function head).isSome = true :=
            congrArg Option.isSome selected
          rw [FilterMap.filterMap_cons_some selected]
          unfold listCountWhere at inductionHypothesis ⊢
          rw [Filter.filter_cons, List.length_cons]
          rw [accepted]
          change Nat.succ (tail.filterMap function).length =
            Nat.succ
              (tail.filter fun value => (function value).isSome).length
          exact congrArg Nat.succ inductionHypothesis

end Purelib.Data.List.CountWhere
