module

public import Init.Data.List.Basic

namespace Purelib.Data.List.DropWhile

universe u

/-- A true head predicate discards that head before continuing the scan.

The retained Boolean equation selects the recursive branch of `dropWhile`
without transporting a proposition about the predicate. -/
public theorem cons_of_true {α : Type u} (predicate : α → Bool)
    (head : α) (tail : List α) (selected : predicate head = true) :
    (head :: tail).dropWhile predicate = tail.dropWhile predicate := by
  change (match predicate head with
    | true => tail.dropWhile predicate
    | false => head :: tail) = tail.dropWhile predicate
  rw [selected]

/-- A false head predicate retains the entire remaining list.

Once the scan reaches a head whose predicate is false, neither that head nor
its tail is removed. -/
public theorem cons_of_false {α : Type u} (predicate : α → Bool)
    (head : α) (tail : List α) (retained : predicate head = false) :
    (head :: tail).dropWhile predicate = head :: tail := by
  change (match predicate head with
    | true => tail.dropWhile predicate
    | false => head :: tail) = head :: tail
  rw [retained]

/-- Repeating the same leading-prefix scan removes no further entries.

The first scan either exhausts the finite list or retains a head whose
Boolean predicate is false. -/
public theorem idempotent {α : Type u} (predicate : α → Bool) :
    ∀ values : List α,
      (values.dropWhile predicate).dropWhile predicate = values.dropWhile predicate
  | [] => rfl
  | head :: tail => by
      cases selected : predicate head with
      | false => rw [cons_of_false predicate head tail selected,
          cons_of_false predicate head tail selected]
      | true =>
          rw [cons_of_true predicate head tail selected]
          exact idempotent predicate tail

/-- Removing a finite leading prefix cannot increase the list length. -/
public theorem length_le {α : Type u} (predicate : α → Bool) :
    ∀ values : List α, (values.dropWhile predicate).length ≤ values.length
  | [] => Nat.le_refl 0
  | head :: tail => by
      cases selected : predicate head with
      | false =>
          rw [cons_of_false predicate head tail selected]
          exact Nat.le_refl _
      | true =>
          rw [cons_of_true predicate head tail selected]
          exact Nat.le.step (length_le predicate tail)

/-- A member retained by a leading-prefix scan belonged to the original list.

The scan either retains the entire original tail or discards a selected head.
Structural recursion transports membership through those actual Boolean branches. -/
public theorem mem_of_mem {α : Type u} (predicate : α → Bool) :
    ∀ {values : List α} {candidate : α}, candidate ∈ values.dropWhile predicate →
      candidate ∈ values
  | [], _, member => by cases member
  | head :: tail, _, member => by
      cases selected : predicate head with
      | false =>
          rw [cons_of_false predicate head tail selected] at member
          exact member
      | true =>
          rw [cons_of_true predicate head tail selected] at member
          exact List.Mem.tail head (mem_of_mem predicate member)

/-- Discarding a selected head strictly decreases the remaining list length.

The retained true predicate removes at least that head; further removals from
the tail can only decrease the length. -/
public theorem length_lt_cons_of_true {α : Type u} (predicate : α → Bool)
    (head : α) (tail : List α) (selected : predicate head = true) :
    ((head :: tail).dropWhile predicate).length < (head :: tail).length := by
  rw [cons_of_true predicate head tail selected]
  exact Nat.succ_le_succ (length_le predicate tail)

/-- Taking and dropping the same selected prefix recovers the original finite list.

Both scans inspect the same Boolean head predicate. A selected head remains in
the taken prefix; the first unselected head and its tail remain in the dropped suffix. -/
public theorem takeWhile_append_dropWhile {Alpha : Type u} (predicate : Alpha → Bool) :
    ∀ values : List Alpha,
      values.takeWhile predicate ++ values.dropWhile predicate = values
  | [] => rfl
  | head :: tail => by
      cases selected : predicate head with
      | false =>
          rewrite [List.takeWhile, selected, cons_of_false predicate head tail selected]
          exact Eq.refl _
      | true =>
          rewrite [List.takeWhile, selected, cons_of_true predicate head tail selected]
          exact congrArg (List.cons head) (takeWhile_append_dropWhile predicate tail)

end Purelib.Data.List.DropWhile
