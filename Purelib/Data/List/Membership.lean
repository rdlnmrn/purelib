module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Tactic.TypeStar

open Purelib

namespace Purelib.Data.List.Membership

/-- A cons occurrence is either the displayed head or an occurrence in the tail.

The two directions retain the actual membership constructors and the equality
with the original head. -/
public theorem mem_cons {Alpha : Type u} {target head : Alpha} {tail : List Alpha} :
    target ∈ head :: tail ↔ target = head ∨ target ∈ tail := by
  constructor
  · intro member
    cases member with
    | head => exact Or.inl rfl
    | tail _ member => exact Or.inr member
  · intro member
    cases member with
    | inl equal => rw [equal]; exact List.Mem.head tail
    | inr member => exact List.Mem.tail head member

/-- A singleton occurrence identifies its sole displayed value.

The head constructor gives equality with that value. An occurrence in the
empty tail is impossible, and equality supplies the head occurrence directly. -/
public theorem mem_singleton {Alpha : Type u} {target head : Alpha} :
    target ∈ [head] ↔ target = head := by
  constructor
  · intro member
    cases member with
    | head => rfl
    | tail _ impossible => nomatch impossible
  · intro equal
    cases equal
    exact List.Mem.head []

end Purelib.Data.List.Membership

namespace Purelib.Data.List.Membership

/-- Every member surviving a finite dropWhile operation belongs to the original list. -/
private theorem mem_of_mem_dropWhile {A : Type*}
    (predicate : A → Bool) (value : A) : ∀ values : List A,
    value ∈ values.dropWhile predicate → value ∈ values
  | [], member => member
  | head :: remaining, member => by
      cases equation : predicate head with
      | false =>
          simpa only [List.dropWhile, equation, Bool.false_eq_true,
            ↓reduceIte] using member
      | true =>
          apply List.mem_cons_of_mem head
          apply mem_of_mem_dropWhile predicate value remaining
          simpa only [List.dropWhile, equation, ↓reduceIte] using member

end Purelib.Data.List.Membership

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

/-- A displayed membership splits a finite list at the displayed occurrence.

The recursive proof retains the actual prefix and suffix; it does not choose
an occurrence from an abstract nonempty set. -/
theorem Membership.split_of_mem {target : Alpha} :
    ∀ {values : List Alpha}, target ∈ values →
      ∃ before after, values = before ++ target :: after
  | [], impossible => by
      nomatch impossible
  | head :: tail, member => by
      cases member with
      | head => exact ⟨[], tail, rfl⟩
      | tail _ tailMember =>
          rcases Membership.split_of_mem tailMember with ⟨before, after, split⟩
          exact ⟨head :: before, after, by rw [split]; rfl⟩

/-- Membership in an appended list is witnessed in one of its original inputs.

The membership constructor retains the selected occurrence. Structural
recursion through the left input transports that witness in both directions. -/
theorem Membership.mem_append {target : Alpha} :
    ∀ {left right : List Alpha}, target ∈ left ++ right ↔ target ∈ left ∨ target ∈ right
  | [], _ => by
      constructor
      · intro member
        exact Or.inr member
      · intro member
        cases member with
        | inl impossible => nomatch impossible
        | inr retained => exact retained
  | head :: left, right => by
      constructor
      · intro member
        cases member with
        | head => exact Or.inl (List.Mem.head left)
        | tail _ tail =>
            cases (Membership.mem_append (left := left) (right := right)).mp tail with
            | inl retained => exact Or.inl (List.Mem.tail head retained)
            | inr retained => exact Or.inr retained
      · intro member
        cases member with
        | inl retained =>
            cases retained with
            | head => exact List.Mem.head _
            | tail _ tail =>
                exact List.Mem.tail head
                  ((Membership.mem_append (left := left) (right := right)).mpr (Or.inl tail))
        | inr retained =>
            exact List.Mem.tail head
              ((Membership.mem_append (left := left) (right := right)).mpr (Or.inr retained))

/-- Every member of a replicated list equals the retained repeated value.

An empty replication has no occurrence. Each successor replication contributes
the repeated value at its head and retains the same value in its tail. -/
theorem Membership.eq_of_mem_replicate {target value : Alpha} :
    ∀ {count : Nat}, target ∈ List.replicate count value → target = value
  | 0, impossible => nomatch impossible
  | count + 1, member => by
      cases member with
      | head => rfl
      | tail _ tail => exact Membership.eq_of_mem_replicate (count := count) tail

namespace Membership

/-- A successful Boolean membership scan supplies its actual list occurrence.

Lawful Boolean equality identifies the selected head with the target.
An unsuccessful head comparison retains the scan's original tail witness. -/
public theorem mem_of_elem_eq_true [BEq Alpha] [LawfulBEq Alpha] {target : Alpha} :
    ∀ {values : List Alpha}, List.elem target values = true → target ∈ values
  | [], impossible => nomatch impossible
  | head :: tail, found => by
      change (match target == head with
        | true => true
        | false => List.elem target tail) = true at found
      cases tested : target == head with
      | false =>
          rw [tested] at found
          exact List.Mem.tail head (mem_of_elem_eq_true found)
      | true =>
          have equal : target = head := eq_of_beq tested
          cases equal
          exact List.Mem.head tail

/-- An actual list occurrence makes the original Boolean membership scan succeed.

Reflexive Boolean equality certifies a head occurrence. A tail occurrence
remains a successful scan whether the current head comparison succeeds or fails. -/
public theorem elem_eq_true_of_mem [BEq Alpha] [ReflBEq Alpha] {target : Alpha}
    {values : List Alpha} (member : target ∈ values) : List.elem target values = true := by
  induction member with
  | head tail =>
      change (match target == target with
        | true => true
        | false => List.elem target tail) = true
      rw [BEq.rfl]
  | tail head _ ih =>
      change (match target == head with
        | true => true
        | false => List.elem target _) = true
      cases target == head with
      | false => exact ih
      | true => rfl

/-- Decide list membership by the original lawful Boolean equality scan.

The exact `List.elem` computation is retained, with structural certificates
for both outcomes. Ordinary synthesis uses these certificates, and
`open scoped Purelib.Data.List.Membership` retains the same registration.
The priority replaces the upstream proof adapter while preserving higher-priority
and explicitly supplied local decision records. -/
public scoped instance (priority := 1001) decidableMem [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha) : Decidable (target ∈ values) :=
  decidable_of_decidable_of_iff
    (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

attribute [instance 1001] decidableMem

end Membership
end Purelib.Data.List

end

end

namespace Purelib.Data.List.Membership

/-- Split a membership indicator at a head absent from its retained tail.

The absence certificate excludes a second occurrence of the head.
Explicit membership constructors identify the head and tail indicator cases. -/
public theorem member_indicator_cons {Alpha : Type u} [DecidableEq Alpha]
    (selected head : Alpha) (tail : List Alpha) (absent : head ∉ tail) :
    (if selected ∈ head :: tail then (1 : Int) else 0) =
      (if head = selected then 1 else 0) + (if selected ∈ tail then 1 else 0) := by
  by_cases same : head = selected
  · cases same
    have present : selected ∈ selected :: tail := List.Mem.head tail
    rw [if_pos present, if_pos rfl, if_neg absent]
    rfl
  · have different : selected ≠ head := fun equal => same equal.symm
    by_cases member : selected ∈ tail
    · have present : selected ∈ head :: tail := List.Mem.tail head member
      rw [if_neg same, if_pos present, if_pos member]
      rfl
    · have absentCons : selected ∉ head :: tail := by
        intro inCons
        cases inCons with
        | head => exact different rfl
        | tail _ inTail => exact member inTail
      rw [if_neg same, if_neg absentCons, if_neg member]
      rfl

/-- Decide list membership by the supplied equality decisions on its ordered entries.

Each displayed head is compared before its original tail. Equal heads provide
that occurrence; unequal heads retain either the recursive occurrence or its
pointwise absence evidence. -/
public def decideEq {Alpha : Type u} [DecidableEq Alpha] (value : Alpha) :
    (values : List Alpha) → Decidable (value ∈ values)
  | [] => isFalse fun impossible => by nomatch impossible
  | head :: tail =>
      match decEq value head with
      | isTrue equal => isTrue (mem_cons.mpr (Or.inl equal))
      | isFalse different =>
          match decideEq value tail with
          | isTrue member => isTrue (List.Mem.tail head member)
          | isFalse notMember => isFalse fun member => by
              rcases mem_cons.mp member with equal | tailMember
              · exact different equal
              · exact notMember tailMember

/-- A retained member different from the displayed head belongs to the original tail.

The head occurrence would identify the two displayed values. Its excluded equality
leaves the same occurrence in the retained tail list. -/
public theorem tail_member {Alpha : Type u} {head cell : Alpha} {tail : List Alpha}
    (member : cell ∈ head :: tail) (different : head ≠ cell) : cell ∈ tail := by
  rcases mem_cons.mp member with equal | member
  · exact (different equal.symm).elim
  · exact member

end Purelib.Data.List.Membership

namespace Purelib.Data.List.Membership

/-- An occurrence after dropping heads remains in the original retained list.

Structural recursion retains the exact occurrence in the original tail and
prepends each discarded head without changing the entry or its membership. -/
public theorem mem_of_mem_drop {Alpha : Type} {entry : Alpha} {values : List Alpha}
    {count : Nat} (member : entry ∈ values.drop count) : entry ∈ values := by
  induction count generalizing values with
  | zero => exact member
  | succ count ih =>
      cases values with
      | nil => exact member
      | cons head tail => exact List.Mem.tail head (ih member)

end Purelib.Data.List.Membership
