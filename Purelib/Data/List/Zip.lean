module

import Init.Data.List.Basic
import Purelib.Data.List.Membership

namespace Purelib.Data.List.Zip

/-- Pairwise mapping produces at most one entry per original left-list entry.

The traversal stops when either retained input list is empty. A pair of
nonempty inputs contributes one output and recurses on the original tails. -/
public theorem length_zipWith_le_left {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    (function : Alpha → Beta → Gamma) : ∀ left right,
      (List.zipWith function left right).length ≤ left.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | _ :: tail, _ :: otherTail => by
      rw [List.zipWith_cons_cons]
      exact Nat.succ_le_succ (length_zipWith_le_left function tail otherTail)

/-- Pairwise mapping of two equally long retained lists preserves their length.

The supplied length equality excludes an unmatched head. Every matched pair
contributes one entry, and successor injectivity retains equality of the tails. -/
public theorem length_zipWith_of_length_eq {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    (function : Alpha → Beta → Gamma) : ∀ left right,
      left.length = right.length →
      (List.zipWith function left right).length = left.length
  | [], [], _ => rfl
  | [], _ :: _, equal => by exact Nat.noConfusion equal
  | _ :: _, [], equal => by exact Nat.noConfusion equal
  | _ :: tail, _ :: otherTail, equal => by
      rw [List.zipWith_cons_cons]
      exact congrArg Nat.succ
        (length_zipWith_of_length_eq function tail otherTail (Nat.succ.inj equal))

/-- The first projection of a zip retains every left entry when the right list is long enough.

The length bound excludes an unmatched left head. Each matched pair retains
its original first coordinate and recurses on the two original tails. -/
public theorem map_fst_zip {Alpha : Type u} {Beta : Type v} :
    ∀ {left : List Alpha} {right : List Beta}, left.length ≤ right.length →
      (left.zip right).map Prod.fst = left
  | [], _, _ => rfl
  | _ :: _, [], bound => False.elim (Nat.not_succ_le_zero _ bound)
  | head :: tail, other :: remaining, bound => by
      change head :: (tail.zip remaining).map Prod.fst = head :: tail
      exact congrArg (List.cons head) (map_fst_zip (Nat.le_of_succ_le_succ bound))

/-- The second projection of a zip retains every right entry when the left list is long enough.

The length bound excludes an unmatched right head. Each matched pair retains
its original second coordinate and recurses on the two original tails. -/
public theorem map_snd_zip {Alpha : Type u} {Beta : Type v} :
    ∀ {left : List Alpha} {right : List Beta}, right.length ≤ left.length →
      (left.zip right).map Prod.snd = right
  | left, [], _ => by cases left <;> rfl
  | [], _ :: _, bound => False.elim (Nat.not_succ_le_zero _ bound)
  | head :: tail, other :: remaining, bound => by
      change other :: (tail.zip remaining).map Prod.snd = other :: remaining
      exact congrArg (List.cons other) (map_snd_zip (Nat.le_of_succ_le_succ bound))

/-- Every paired zip occurrence retains an occurrence of both original coordinates.

A head occurrence identifies the displayed pair. A tail occurrence gives the
two retained tail memberships, which are inserted into the original lists. -/
public theorem of_mem_zip {Alpha : Type u} {Beta : Type v} {first : Alpha} {second : Beta} :
    ∀ {left : List Alpha} {right : List Beta}, (first, second) ∈ left.zip right →
      first ∈ left ∧ second ∈ right
  | [], right, member => by cases right <;> nomatch member
  | _ :: _, [], member => nomatch member
  | head :: tail, other :: remaining, member => by
      change (first, second) ∈ (head, other) :: tail.zip remaining at member
      cases Membership.mem_cons.mp member with
      | inl equal =>
          cases equal
          exact ⟨List.Mem.head tail, List.Mem.head remaining⟩
      | inr member =>
          have retained := of_mem_zip member
          exact ⟨List.Mem.tail head retained.1, List.Mem.tail other retained.2⟩

/-- Zipping lists with equal ordered key projections pairs entries with equal keys.

Each head pair inherits the head equality. A retained tail occurrence uses the
equality of the two original mapped tails, without changing either traversal. -/
public theorem keys_eq_of_mem_zip {A : Type u} {B : Type v} {Key : Type w} (first : A → Key) (last : B → Key) :
    ∀ (xs : List A) (ys : List B), xs.map first = ys.map last →
      ∀ pair ∈ xs.zip ys, first pair.1 = last pair.2
  | [], _, _, _, member => by cases member
  | _ :: _, [], equal, _, _ => by cases equal
  | x :: xs, y :: ys, equal, pair, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same; exact (List.cons.inj equal).1
      · exact keys_eq_of_mem_zip first last xs ys (List.cons.inj equal).2 pair member

end Purelib.Data.List.Zip
