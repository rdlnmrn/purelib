module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.List

open Purelib.Geometry.Rational (Box)

open Purelib.Geometry.Rational.Box.Separation

section
/-!
# Structural finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

public section

namespace Purelib.Data.List

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Pairwise relatedness is preserved and reflected by a finite map.

Each mapped occurrence retains its original source witness. The head relation
and tail certificate are transported separately by structural recursion. -/
theorem Pairwise.pairwise_map {function : Alpha → Beta}
    {relation : Beta → Beta → Prop} :
    ∀ {values : List Alpha},
      (values.map function).Pairwise relation ↔
        values.Pairwise
          (fun left right => relation (function left) (function right))
  | [] => by
      constructor <;> intro _ <;> exact List.Pairwise.nil
  | head :: tail => by
      change (function head :: tail.map function).Pairwise relation ↔
        (head :: tail).Pairwise (fun left right => relation (function left) (function right))
      constructor
      · intro pairwise
        rcases List.pairwise_cons.mp pairwise with ⟨headRelated, tailRelated⟩
        exact List.pairwise_cons.mpr ⟨fun value member =>
          headRelated (function value) (Map.mem_map_of_mem member),
          Pairwise.pairwise_map.mp tailRelated⟩
      · intro pairwise
        rcases List.pairwise_cons.mp pairwise with ⟨headRelated, tailRelated⟩
        apply List.pairwise_cons.mpr
        refine ⟨?_, Pairwise.pairwise_map.mpr tailRelated⟩
        intro mapped mappedMember
        rcases Map.mem_map.mp mappedMember with
          ⟨source, sourceMember, equal⟩
        exact equal ▸ headRelated source sourceMember

/-- A singleton list is pairwise related for any displayed binary relation. -/
theorem Pairwise.pairwise_singleton (relation : Alpha → Alpha → Prop)
    (value : Alpha) : [value].Pairwise relation := by
  apply List.pairwise_cons.mpr
  constructor
  · intro other impossible
    nomatch impossible
  · exact List.Pairwise.nil

/-- Assemble pairwise relatedness of two appended finite lists.

The two original internal certificates and the supplied ordered cross-list
relations certify every occurrence in the concatenation. -/
theorem Pairwise.pairwise_append {relation : Alpha → Alpha → Prop} :
    ∀ {left right : List Alpha}, left.Pairwise relation →
      right.Pairwise relation →
      (∀ leftValue ∈ left, ∀ rightValue ∈ right,
        relation leftValue rightValue) →
      (left ++ right).Pairwise relation
  | [], _, _, rightPairwise, _ => rightPairwise
  | head :: tail, right, leftPairwise, rightPairwise, cross => by
      apply List.pairwise_cons.mpr
      constructor
      · intro value member
        rcases Membership.mem_append.mp member with tailMember | rightMember
        · exact (List.pairwise_cons.mp leftPairwise).1 value tailMember
        · exact cross head List.mem_cons_self value rightMember
      · exact Pairwise.pairwise_append (List.pairwise_cons.mp leftPairwise).2
          rightPairwise (fun leftValue leftMember =>
            cross leftValue (List.mem_cons_of_mem head leftMember))

/-- Removing one displayed middle entry preserves pairwise relatedness.

The retained prefix and suffix keep their original occurrence relations.
Structural recursion transports membership around the removed entry. -/
theorem Pairwise.pairwise_remove_middle {relation : Alpha → Alpha → Prop}
    {middle : Alpha} :
    ∀ {before after : List Alpha},
      (before ++ middle :: after).Pairwise relation →
        (before ++ after).Pairwise relation
  | [], _, pairwise => (List.pairwise_cons.mp pairwise).2
  | head :: tail, after, pairwise => by
      rcases List.pairwise_cons.mp pairwise with ⟨headAll, restPairwise⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, Pairwise.pairwise_remove_middle restPairwise⟩
      intro value member
      rcases Membership.mem_append.mp member with tailMember | afterMember
      · exact headAll value
          (Membership.mem_append.mpr (Or.inl tailMember))
      · exact headAll value
          (Membership.mem_append.mpr
            (Or.inr (List.mem_cons_of_mem middle afterMember)))

/-- A pairwise list certificate relates the entries at any two increasing bounded
indices.

Both original list bounds and the strict index order are retained explicitly,
allowing each indexed entry to be read from the same list. -/
theorem Pairwise.pairwise_getElem {relation : Alpha → Alpha → Prop}
    {values : List Alpha} (pairwise : values.Pairwise relation) :
    ∀ (left right : Nat) (leftBound : left < values.length)
      (rightBound : right < values.length),
      left < right → relation values[left] values[right] := by
  induction values with
  | nil =>
      intro left _ leftBound
      nomatch leftBound
  | cons head tail inductionHypothesis =>
      intro left right leftBound rightBound ordered
      cases left with
      | zero =>
          cases right with
          | zero => exact False.elim (Nat.lt_irrefl 0 ordered)
          | succ right =>
              have tailBound : right < tail.length :=
                Nat.lt_of_succ_lt_succ rightBound
              exact (List.pairwise_cons.mp pairwise).1 tail[right]
                (List.getElem_mem tailBound)
      | succ left =>
          cases right with
          | zero =>
              exact False.elim (Nat.not_lt_zero (Nat.succ left) ordered)
          | succ right =>
              have leftTailBound : left < tail.length :=
                Nat.lt_of_succ_lt_succ leftBound
              have rightTailBound : right < tail.length :=
                Nat.lt_of_succ_lt_succ rightBound
              have tailOrdered : left < right :=
                Nat.lt_of_succ_lt_succ ordered
              exact inductionHypothesis
                (List.pairwise_cons.mp pairwise).2 left right
                leftTailBound rightTailBound tailOrdered

/-- Moving a middle entry to the front preserves a symmetric pairwise relation.

The equivalence retains the original prefix, suffix and middle entry. Only
relations involving the moved entry need the supplied symmetry certificate. -/
theorem Pairwise.pairwise_middle {R : Alpha → Alpha → Prop}
    (symmetric : ∀ {left right}, R left right → R right left)
    {middle : Alpha} {left right : List Alpha} :
    (left ++ middle :: right).Pairwise R ↔
      (middle :: (left ++ right)).Pairwise R := by
  constructor
  · intro pairwise
    induction left with
    | nil => exact pairwise
    | cons head tail inductionHypothesis =>
        rcases List.pairwise_cons.mp pairwise with
          ⟨headAll, tailPairwise⟩
        have movedTail := inductionHypothesis tailPairwise
        rcases List.pairwise_cons.mp movedTail with
          ⟨middleAll, remainingPairwise⟩
        apply List.pairwise_cons.mpr
        refine ⟨?_, List.pairwise_cons.mpr
          ⟨?_, remainingPairwise⟩⟩
        · intro value member
          cases member with
          | head => exact symmetric (headAll middle
              (Membership.mem_append.mpr (Or.inr List.mem_cons_self)))
          | tail _ remainingMember => exact middleAll value remainingMember
        · intro value member
          rcases Membership.mem_append.mp member with tailMember | rightMember
          · exact headAll value
              (Membership.mem_append.mpr (Or.inl tailMember))
          · exact headAll value (Membership.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem middle rightMember)))
  · intro pairwise
    induction left with
    | nil => exact pairwise
    | cons head tail inductionHypothesis =>
        rcases List.pairwise_cons.mp pairwise with
          ⟨middleAll, headRemainingPairwise⟩
        rcases List.pairwise_cons.mp headRemainingPairwise with
          ⟨headAll, remainingPairwise⟩
        have movedTail : (middle :: tail ++ right).Pairwise R :=
          List.pairwise_cons.mpr ⟨fun value member =>
            middleAll value (List.mem_cons_of_mem head member),
            remainingPairwise⟩
        have tailPairwise := inductionHypothesis movedTail
        apply List.pairwise_cons.mpr
        refine ⟨?_, tailPairwise⟩
        intro value member
        rcases Membership.mem_append.mp member with tailMember | middleRightMember
        · exact headAll value
            (Membership.mem_append.mpr (Or.inl tailMember))
        · cases middleRightMember with
          | head => exact symmetric (middleAll head List.mem_cons_self)
          | tail _ rightMember =>
              exact headAll value (Membership.mem_append.mpr (Or.inr rightMember))

end Purelib.Data.List

end

end

section
@[expose] public section

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace Purelib.Data.List.Pairwise

/-- Any two distinct retained indices in a pairwise-separated box list select separated
boxes.

Use their natural index order for the list certificate and the symmetry of box
separation when the indices occur in the reverse order. -/
theorem pairwise_get_separated
    {boxes : List Box} (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (left right : Fin boxes.length) (different : left ≠ right) :
    (boxes.get left).Separated (boxes.get right) := by
  by_cases ordered : left.val < right.val
  · exact pairwise_getElem pairwise left.val right.val
      left.isLt right.isLt ordered
  · have unequalValues : left.val ≠ right.val :=
      fun equal => different (Fin.ext equal)
    have reversed : right.val < left.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) unequalValues.symm
    exact Box.separated_symm
      (pairwise_getElem pairwise right.val left.val
        right.isLt left.isLt reversed)
end Purelib.Data.List.Pairwise

end

section
@[expose] public section

/-!
# Ordered retained list entries

A pairwise relation holds between retained entries whose finite indices are ordered.
-/

namespace Purelib.Data.List.Pairwise

/-- A pairwise certificate relates two retained list indices ordered by their natural
values. -/
public theorem pairwise_get_of_val_lt
    {α : Type} {relation : α → α → Prop} {values : List α}
    (pairwise : values.Pairwise relation)
    (left right : Fin values.length) (ordered : left.val < right.val) :
    relation (values.get left) (values.get right) := by
  have direct := pairwise_getElem pairwise left.val right.val
    left.isLt right.isLt ordered
  exact direct

end Purelib.Data.List.Pairwise

end

namespace Purelib.Data.List.Pairwise

open Purelib.Data.Rat

/-- Equal rational keys identify equal entries of a strictly ordered list.

The original pairwise strict key order separates each head from its retained
tail. Two displayed entries with equal keys therefore have the same occurrence. -/
public theorem ordered_eq {Alpha : Type} {key : Alpha → Fraction.Rational} {entries : List Alpha}
    (ordered : entries.Pairwise (fun first second => key first < key second))
    {first second : Alpha} (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (same : key first = key second) : first = second := by
  induction entries with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with equal | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with equal | secondMember
        · exact equal.symm
        · exact (ne_of_lt ((List.pairwise_cons.mp ordered).1 second secondMember) same).elim
      · rcases Membership.mem_cons.mp secondMember with equal | secondMember
        · subst second
          exact (ne_of_lt ((List.pairwise_cons.mp ordered).1 first firstMember) same.symm).elim
        · exact ih (List.pairwise_cons.mp ordered).2 firstMember secondMember

end Purelib.Data.List.Pairwise
