module
import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Multiplication
import Mathlib.Data.List.Defs

namespace Purelib.Data.List.Filter

/-- Filtering a displayed head selects its retained Boolean branch.

The tail is filtered by the same predicate in either branch. An accepted head
is retained in its original position; a rejected head contributes no entry. -/
public theorem filter_cons {Alpha : Type u} (predicate : Alpha → Bool)
    (head : Alpha) (tail : List Alpha) :
    (head :: tail).filter predicate =
      if predicate head then head :: tail.filter predicate else tail.filter predicate := by
  change (match predicate head with
    | true => head :: tail.filter predicate
    | false => tail.filter predicate) = _
  cases predicate head <;> rfl

/-- Filtering an accepted head retains it before the filtered tail.

The supplied true Boolean result selects the head branch of the original
filter. The remaining entries are filtered with the same predicate. -/
public theorem filter_cons_of_pos {Alpha : Type u} {predicate : Alpha → Bool}
    {head : Alpha} {tail : List Alpha} (accepted : predicate head = true) :
    (head :: tail).filter predicate = head :: tail.filter predicate := by
  change (match predicate head with
    | true => head :: tail.filter predicate
    | false => tail.filter predicate) = _
  rw [accepted]

/-- Filtering a rejected head returns the filtered tail.

The supplied rejection excludes the true Boolean branch. The original head
contributes no entry, and the tail keeps the same filtering predicate. -/
public theorem filter_cons_of_neg {Alpha : Type u} {predicate : Alpha → Bool}
    {head : Alpha} {tail : List Alpha} (rejected : ¬ predicate head = true) :
    (head :: tail).filter predicate = tail.filter predicate := by
  cases selected : predicate head with
  | false =>
      change (match predicate head with
        | true => head :: tail.filter predicate
        | false => tail.filter predicate) = _
      rw [selected]
  | true => exact False.elim (rejected selected)

/-- Filtering a concatenation concatenates the two filtered lists.

The original left and right spines keep their occurrence order and
multiplicity. Structural recursion compares only the retained head branch. -/
public theorem filter_append {Alpha : Type u} (predicate : Alpha → Bool)
    (left right : List Alpha) :
    (left ++ right).filter predicate = left.filter predicate ++ right.filter predicate := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      change (head :: (tail ++ right)).filter predicate = _
      cases selected : predicate head with
      | false =>
          rw [filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible),
            filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible)]
          exact ih
      | true =>
          rw [filter_cons_of_pos selected, filter_cons_of_pos selected]
          exact congrArg (List.cons head) ih

/-- A filtered member retains its source occurrence and acceptance certificate.

Membership is equivalent to occurrence in the original list together with a
true Boolean predicate. Both directions retain the actual list constructors. -/
public theorem mem_filter {Alpha : Type u} {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha},
      target ∈ values.filter predicate ↔ target ∈ values ∧ predicate target = true
  | [] => by
      constructor
      · intro impossible; nomatch impossible
      · rintro ⟨impossible, _⟩; nomatch impossible
  | head :: tail => by
      cases selected : predicate head with
      | false =>
          rw [filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible)]
          constructor
          · intro member
            rcases (mem_filter (values := tail)).mp member with ⟨source, accepted⟩
            exact ⟨List.Mem.tail head source, accepted⟩
          · rintro ⟨source, accepted⟩
            cases source with
            | head => exact False.elim (Bool.noConfusion (selected.symm.trans accepted))
            | tail _ member => exact (mem_filter (values := tail)).mpr ⟨member, accepted⟩
      | true =>
          rw [filter_cons_of_pos selected]
          constructor
          · intro member
            cases member with
            | head => exact ⟨List.Mem.head tail, selected⟩
            | tail _ member =>
                rcases (mem_filter (values := tail)).mp member with ⟨source, accepted⟩
                exact ⟨List.Mem.tail head source, accepted⟩
          · rintro ⟨source, accepted⟩
            cases source with
            | head => exact List.Mem.head _
            | tail _ member =>
                exact List.Mem.tail head ((mem_filter (values := tail)).mpr ⟨member, accepted⟩)

/-- Filtering preserves each ordered pairwise relation of the original list.

Every surviving occurrence retains its source membership. The original head
relation and tail certificate therefore certify the filtered list directly. -/
public theorem pairwise_filter {Alpha : Type u} {relation : Alpha → Alpha → Prop}
    (predicate : Alpha → Bool) :
    ∀ {values : List Alpha}, values.Pairwise relation →
      (values.filter predicate).Pairwise relation
  | [], _ => List.Pairwise.nil
  | head :: tail, pairwise => by
      cases selected : predicate head with
      | false =>
          rw [filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible)]
          exact pairwise_filter predicate (List.pairwise_cons.mp pairwise).2
      | true =>
          rw [filter_cons_of_pos selected]
          apply List.pairwise_cons.mpr
          refine ⟨?_, pairwise_filter predicate (List.pairwise_cons.mp pairwise).2⟩
          intro value member
          exact (List.pairwise_cons.mp pairwise).1 value (mem_filter.mp member).1

/-- Filtering cannot increase the displayed list length.

An accepted head contributes one successor to both lengths. A rejected head
leaves the filtered tail, whose bound is retained under the source successor. -/
public theorem length_filter_le {Alpha : Type u} (predicate : Alpha → Bool)
    (values : List Alpha) : (values.filter predicate).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      cases selected : predicate head with
      | false =>
          rw [filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible)]
          exact Nat.le_trans ih (Nat.le_succ tail.length)
      | true =>
          rw [filter_cons_of_pos selected]
          exact Nat.succ_le_succ ih

/-- Rejecting every entry gives the empty filtered list.

The constant false predicate rejects each displayed head, and structural
recursion retains the same rejected tail without a proposition rewrite. -/
public theorem filter_false {Alpha : Type u} :
    (values : List Alpha) → values.filter (fun _ => false) = []
  | [] => rfl
  | head :: tail => by
      rw [filter_cons_of_neg (by intro impossible; nomatch impossible)]
      exact filter_false tail

open Purelib.Data.List

/-- Filtering by a conjunction equals filtering successively by its two Boolean
predicates.

Both procedures retain exactly the entries accepted by both tests, preserving
the original source order and every accepted occurrence. -/
public theorem filter_and_eq_filter_filter {Alpha : Type*}
    (values : List Alpha) (first second : Alpha → Bool) :
    values.filter (fun value => first value && second value) =
      (values.filter first).filter second := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [Filter.filter_cons, Filter.filter_cons]
      cases firstAccepted : first head with
      | false =>
          rw [Bool.false_and]
          exact inductionHypothesis
      | true =>
          rw [Bool.true_and, if_pos rfl, Filter.filter_cons]
          cases secondAccepted : second head with
          | false =>
              have falseNeTrue : ¬ false = true := by
                intro impossible
                exact Bool.noConfusion impossible
              rw [if_neg falseNeTrue, if_neg falseNeTrue]
              exact inductionHypothesis
          | true =>
              rw [if_pos rfl, if_pos rfl, inductionHypothesis]

/-- Filtering out an absent target preserves the entire list.

The supplied equality decision rejects the target at every source occurrence.
Structural recursion keeps each original head and its ordered tail. -/
public theorem filter_ne_target_eq_self {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, (∀ value ∈ values, value ≠ target) →
      (letI : DecidableEq Alpha := eqDecidable
       values.filter fun value => value ≠ target) = values
  | [], _ => rfl
  | head :: tail, allDifferent => by
      letI : DecidableEq Alpha := eqDecidable
      rw [Filter.filter_cons_of_pos
        (predicate := fun value : Alpha => decide (value ≠ target))
        (decide_eq_true (allDifferent head List.mem_cons_self))]
      rw [filter_ne_target_eq_self eqDecidable target (fun value member =>
        allDifferent value (List.mem_cons_of_mem head member))]

/-- Removing a present target from a duplicate-free list shortens its length by exactly
one.

The supplied equality decision drives the filter; duplicate-freeness ensures that all
entries except the unique target remain in their original order. -/
public theorem filter_ne_target_length_add_one {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, values.Nodup → target ∈ values →
      (letI : DecidableEq Alpha := eqDecidable
       (values.filter fun value => value ≠ target).length + 1) = values.length
  | [], _, impossible => nomatch impossible
  | head :: tail, nodup, targetMember => by
      letI : DecidableEq Alpha := eqDecidable
      cases eqDecidable head target with
      | isTrue headTarget =>
          have tailDifferent : ∀ value ∈ tail, value ≠ target := by
            intro value member valueTarget
            apply (List.pairwise_cons.mp nodup).1 value member
            exact headTarget.trans valueTarget.symm
          rw [Filter.filter_cons_of_neg
            (predicate := fun value : Alpha => decide (value ≠ target))
            (fun accepted => (of_decide_eq_true accepted) headTarget)]
          rw [filter_ne_target_eq_self eqDecidable target tailDifferent]
          rfl
      | isFalse headDifferent =>
          have tailMember : target ∈ tail := by
            cases targetMember with
            | head => exact False.elim (headDifferent rfl)
            | tail _ member => exact member
          rw [Filter.filter_cons_of_pos
            (predicate := fun value : Alpha => decide (value ≠ target))
            (decide_eq_true headDifferent)]
          have induction := filter_ne_target_length_add_one
            eqDecidable target (List.pairwise_cons.mp nodup).2 tailMember
          exact congrArg Nat.succ induction

/-- Pointwise equal Boolean tests retain the same filtered list.

Structural recursion preserves every accepted occurrence in its original
position and applies the supplied equality only to the current entry. -/
public theorem filter_congr {Item : Type} (first second : Item → Bool)
    (equal : ∀ item, first item = second item) (items : List Item) :
    items.filter first = items.filter second := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [filter_cons, filter_cons, equal head, ih]

end Purelib.Data.List.Filter

section
namespace Purelib.Data.List.Filter
open Purelib.Data.List
open Purelib.Data.Nat
open scoped Purelib.Data.Nat

/-- A Boolean filter and its complement partition the length of a finite list. -/
public theorem
  filter_bool_add_complement_length
  {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    (values.filter predicate).length +
      (values.filter fun value => !predicate value).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
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

end Purelib.Data.List.Filter
end
