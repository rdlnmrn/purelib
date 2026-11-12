module
public import Purelib.Data.List.DropWhile.Basic
public import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Tactic.QuotientFreeOmega

/-!
# Finite grouping by nondecreasing natural indices

Each group consumes the next contiguous prefix with its original index. The
remaining suffix is passed to the next group, preserving order and completed
prefix work rather than rescanning the whole original list.
-/

public section

namespace Purelib.Data.List.OrderedGroups

/-- Consume consecutive index groups from an original ordered list.

The next group takes the prefix at the current index. Its retained suffix is
used for the next index; the supplied count bounds the number of groups. -/
@[expose] def groups {α : Type} (index : α → Nat) : Nat → Nat → List α → List (List α)
  | _, 0, _ => []
  | start, count + 1, items =>
      let predicate := fun item => decide (index item = start)
      let group := items.takeWhile predicate
      let remaining := items.dropWhile predicate
      group :: groups index (start + 1) count remaining

/-- The finite grouping retains exactly the requested number of index positions. -/
theorem groups_length {α : Type} (index : α → Nat) : ∀ (count start : Nat) (items : List α),
    (groups index start count items).length = count
  | 0, _, _ => rfl
  | count + 1, start, items => by
      change (groups index (start + 1) count
        (items.dropWhile (fun item => decide (index item = start)))).length + 1 = count + 1
      rw [groups_length index count (start + 1)]

/-- Dropping an initial prefix preserves pairwise order of the retained suffix. -/
private theorem pairwise_drop {α : Type} (predicate : α → Bool) (relation : α → α → Prop) :
    ∀ items : List α, items.Pairwise relation → (items.dropWhile predicate).Pairwise relation
  | [], pairwise => pairwise
  | head :: tail, pairwise => by
      cases selected : predicate head with
      | false =>
          rw [DropWhile.cons_of_false predicate head tail selected]
          exact pairwise
      | true =>
          rw [DropWhile.cons_of_true predicate head tail selected]
          exact pairwise_drop predicate relation tail (List.pairwise_cons.mp pairwise).2

/-- After consuming the current-index prefix, every retained ordered item has a greater index. -/
private theorem drop_index_gt {α : Type} (index : α → Nat) (start : Nat) :
    ∀ items : List α, items.Pairwise (fun first second => index first ≤ index second) →
      (∀ item ∈ items, start ≤ index item) →
        ∀ item ∈ items.dropWhile (fun item => decide (index item = start)), start < index item
  | [], _, _, _, member => by nomatch member
  | head :: tail, pairwise, lower, item, member => by
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      have tailLower : ∀ candidate ∈ tail, start ≤ index candidate :=
        fun candidate present => lower candidate (List.mem_cons_of_mem head present)
      by_cases same : index head = start
      · rw [DropWhile.cons_of_true _ head tail (decide_eq_true same)] at member
        exact drop_index_gt index start tail tailPairwise tailLower item member
      · rw [DropWhile.cons_of_false _ head tail (decide_eq_false same)] at member
        have headGreater : start < index head :=
          Nat.lt_of_le_of_ne (lower head List.mem_cons_self) (fun equal => same equal.symm)
        rcases Purelib.Data.List.Membership.mem_cons.mp member with first | later
        · exact first ▸ headGreater
        · exact Nat.lt_of_lt_of_le headGreater ((List.pairwise_cons.mp pairwise).1 item later)

/-- Every item in a taken index prefix has that exact index. -/
theorem takeWhile_index {α : Type} (index : α → Nat) (start : Nat) :
    ∀ (items : List α) (item : α), item ∈ items.takeWhile (fun item => decide (index item = start)) →
      index item = start
  | [], _, member => by nomatch member
  | head :: tail, item, member => by
      by_cases same : index head = start
      · rw [List.takeWhile, decide_eq_true same] at member
        rcases Purelib.Data.List.Membership.mem_cons.mp member with first | later
        · exact first ▸ same
        · exact takeWhile_index index start tail item later
      · rw [List.takeWhile, decide_eq_false same] at member
        nomatch member

/-- Filtering rejects a finite list when every index differs from the requested one. -/
private theorem filter_none {α : Type} (index : α → Nat) (target : Nat) :
    ∀ items : List α, (∀ item ∈ items, index item ≠ target) →
      items.filter (fun item => decide (index item = target)) = []
  | [], _ => rfl
  | head :: tail, different => by
      have rejected : ¬ decide (index head = target) = true := by
        intro accepted
        exact different head List.mem_cons_self (of_decide_eq_true accepted)
      rw [Filter.filter_cons_of_neg (predicate := fun item => decide (index item = target)) rejected]
      exact filter_none index target tail (fun item member => different item (List.mem_cons_of_mem head member))

/-- On a bounded ordered suffix, the next taken prefix is exactly the current-index filter. -/
theorem takeWhile_eq_filter {α : Type} (index : α → Nat) (start : Nat) :
    ∀ items : List α, items.Pairwise (fun first second => index first ≤ index second) →
      (∀ item ∈ items, start ≤ index item) →
        items.takeWhile (fun item => decide (index item = start)) =
          items.filter (fun item => decide (index item = start))
  | [], _, _ => rfl
  | head :: tail, pairwise, lower => by
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      have tailLower : ∀ item ∈ tail, start ≤ index item :=
        fun item member => lower item (List.mem_cons_of_mem head member)
      by_cases same : index head = start
      · rw [List.takeWhile, decide_eq_true same,
          Filter.filter_cons_of_pos (predicate := fun item => decide (index item = start)) (decide_eq_true same)]
        exact congrArg (List.cons head) (takeWhile_eq_filter index start tail tailPairwise tailLower)
      · rw [List.takeWhile, decide_eq_false same]
        have greater : ∀ item ∈ head :: tail, start < index item := by
          intro item member
          have headGreater : start < index head :=
            Nat.lt_of_le_of_ne (lower head List.mem_cons_self) (fun equal => same equal.symm)
          rcases Purelib.Data.List.Membership.mem_cons.mp member with first | later
          · exact first ▸ headGreater
          · exact Nat.lt_of_lt_of_le headGreater ((List.pairwise_cons.mp pairwise).1 item later)
        exact (filter_none index start (head :: tail)
          (fun item member equal => Nat.lt_irrefl start (equal ▸ greater item member))).symm

/-- Dropping a different-index prefix preserves the original filter for a later index. -/
theorem filter_drop_other {α : Type} (index : α → Nat) (start target : Nat) (different : start ≠ target) :
    ∀ items : List α,
      (items.dropWhile (fun item => decide (index item = start))).filter (fun item => decide (index item = target)) =
        items.filter (fun item => decide (index item = target))
  | [] => rfl
  | head :: tail => by
      by_cases same : index head = start
      · rw [DropWhile.cons_of_true _ head tail (decide_eq_true same)]
        have rejected : ¬ decide (index head = target) = true := by
          intro accepted
          exact different (same.symm.trans (of_decide_eq_true accepted))
        rw [Filter.filter_cons_of_neg (predicate := fun item => decide (index item = target)) rejected]
        exact filter_drop_other index start target different tail
      · rw [DropWhile.cons_of_false _ head tail (decide_eq_false same)]

/-- Flattening bounded nondecreasing index groups recovers the exact original ordered list.

Every original index lies in the supplied half-open range. Each step takes
its current prefix and passes the untouched suffix to the next group. -/
theorem groups_flatten {α : Type} (index : α → Nat) : ∀ (count start : Nat) (items : List α),
    items.Pairwise (fun first second => index first ≤ index second) →
    (∀ item ∈ items, start ≤ index item ∧ index item < start + count) →
      (groups index start count items).flatten = items
  | 0, start, [], _, _ => rfl
  | 0, start, head :: tail, _, bounds => by
      have bound := bounds head List.mem_cons_self
      have impossible : index head < start := by
        simpa only [Nat.add_zero] using bound.2
      exact (Nat.not_lt_of_ge bound.1 impossible).elim
  | count + 1, start, items, pairwise, bounds => by
      let predicate := fun item => decide (index item = start)
      let remaining := items.dropWhile predicate
      have ordered : remaining.Pairwise (fun first second => index first ≤ index second) :=
        pairwise_drop predicate _ items pairwise
      have greater := drop_index_gt index start items pairwise (fun item member => (bounds item member).1)
      have nextBounds : ∀ item ∈ remaining, start + 1 ≤ index item ∧ index item < (start + 1) + count := by
        intro item member
        have original := bounds item (DropWhile.mem_of_mem predicate member)
        have upper := original.2
        clear original
        have above := greater item member
        constructor
        · exact Nat.succ_le_of_lt above
        · omega0
      have rest := groups_flatten index count (start + 1) remaining ordered nextBounds
      change items.takeWhile predicate ++ (groups index (start + 1) count remaining).flatten = items
      rw [rest]
      exact DropWhile.takeWhile_append_dropWhile predicate items

/-- A bounded group is exactly the original ordered filter for its retained index.

The supplied index offset lies in the group count. Earlier consumed prefixes
have different indices, so the same original occurrences remain in the group. -/
theorem groups_getElem? {α : Type} (index : α → Nat) :
    ∀ (count start : Nat) (items : List α) (offset : Nat), offset < count →
      items.Pairwise (fun first second => index first ≤ index second) →
      (∀ item ∈ items, start ≤ index item ∧ index item < start + count) →
        Purelib.Data.List.getElem? (groups index start count items) offset =
          some (items.filter (fun item => decide (index item = start + offset)))
  | 0, _, _, offset, impossible, _, _ => (Nat.not_lt_zero offset impossible).elim
  | count + 1, start, items, 0, _, pairwise, bounds => by
      change some (items.takeWhile (fun item => decide (index item = start))) =
        some (items.filter (fun item => decide (index item = start + 0)))
      rw [Nat.add_zero, takeWhile_eq_filter index start items pairwise (fun item member => (bounds item member).1)]
  | count + 1, start, items, offset + 1, below, pairwise, bounds => by
      let predicate := fun item => decide (index item = start)
      let remaining := items.dropWhile predicate
      have ordered : remaining.Pairwise (fun first second => index first ≤ index second) :=
        pairwise_drop predicate _ items pairwise
      have greater := drop_index_gt index start items pairwise (fun item member => (bounds item member).1)
      have nextBounds : ∀ item ∈ remaining, start + 1 ≤ index item ∧ index item < (start + 1) + count := by
        intro item member
        have upper := (bounds item (DropWhile.mem_of_mem predicate member)).2
        have above := greater item member
        constructor
        · exact Nat.succ_le_of_lt above
        · omega0
      have retained := groups_getElem? index count (start + 1) remaining offset
        (Nat.lt_of_succ_lt_succ below) ordered nextBounds
      have same : (start + 1) + offset = start + (offset + 1) := by omega0
      rw [same] at retained
      have different : start ≠ start + (offset + 1) := by omega0
      rw [filter_drop_other index start (start + (offset + 1)) different items] at retained
      exact retained

end Purelib.Data.List.OrderedGroups

end
