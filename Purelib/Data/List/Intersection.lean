module
import Purelib.Data.List.Nodup
-- The exposed finite scan retains this exact Boolean membership decision.
public import Purelib.Data.List.Membership
import Purelib.Data.List.Append

open Purelib.Data.List

/-!
# Structural finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

public section

namespace Purelib.Data.List

open scoped Purelib.Data.List.Membership

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Search the left list in order for its first entry also in the right list.

The original lawful Boolean membership scan tests each retained left entry
against the same right list, stopping at the first successful test. -/
@[expose] def Intersection.firstIntersection? [DecidableEq Alpha] :
    List Alpha → List Alpha → Option Alpha
  | [], _ => none
  | head :: tail, right =>
      if head ∈ right then some head else Intersection.firstIntersection? tail right

/-- A successful intersection search returns an occurrence in both inputs.

The first successful head retains its actual right-list membership witness.
An unsuccessful head test transports the result from the unchanged left tail. -/
theorem Intersection.firstIntersection?_eq_some [DecidableEq Alpha]
    {target : Alpha} :
    ∀ {left right : List Alpha},
      Intersection.firstIntersection? left right = some target →
        target ∈ left ∧ target ∈ right
  | [], _, impossible => by
      nomatch impossible
  | head :: tail, right, found => by
      by_cases headMember : head ∈ right
      · rw [Intersection.firstIntersection?, if_pos headMember] at found
        injection found with equal
        cases equal
        exact ⟨List.Mem.head tail, headMember⟩
      · rw [Intersection.firstIntersection?, if_neg headMember] at found
        rcases Intersection.firstIntersection?_eq_some found with
          ⟨tailMember, rightMember⟩
        exact ⟨List.mem_cons_of_mem head tailMember, rightMember⟩

/-- A failed intersection search certifies that every cross-list pair is unequal.

The negative head decision rejects its actual right-list occurrences, and
the retained tail failure certifies each remaining left occurrence. -/
theorem Intersection.firstIntersection?_eq_none [DecidableEq Alpha] :
    ∀ {left right : List Alpha},
      Intersection.firstIntersection? left right = none →
        ∀ leftValue ∈ left, ∀ rightValue ∈ right,
          leftValue ≠ rightValue
  | [], _, _, _, impossible => by
      nomatch impossible
  | head :: tail, right, failed, leftValue, leftMember => by
      by_cases headMember : head ∈ right
      · rw [Intersection.firstIntersection?, if_pos headMember] at failed
        nomatch failed
      · rw [Intersection.firstIntersection?, if_neg headMember] at failed
        cases leftMember with
        | head =>
            intro rightValue rightMember equal
            cases equal
            exact headMember rightMember
        | tail _ tailMember =>
            exact Intersection.firstIntersection?_eq_none failed leftValue tailMember

/-- Two lists exceeding their common duplicate-free carrier must intersect.

The actual combined lengths exceed the supplied carrier's length. Its
containment and duplicate-freeness certificates rule out a failed ordered
intersection scan on the original input lists. -/
theorem Intersection.firstIntersection?_ne_none_of_length_gt [DecidableEq Alpha]
    {left right carrier : List Alpha}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (leftContained : ∀ value ∈ left, value ∈ carrier)
    (rightContained : ∀ value ∈ right, value ∈ carrier)
    (carrierNodup : carrier.Nodup)
    (oversized : carrier.length < left.length + right.length) :
    Intersection.firstIntersection? left right ≠ none := by
  intro failed
  have appendedNodup : (left ++ right).Nodup :=
    Nodup.nodup_append leftNodup rightNodup
      (Intersection.firstIntersection?_eq_none failed)
  have appendedContained :
      ∀ value ∈ left ++ right, value ∈ carrier := by
    intro value member
    rcases Membership.mem_append.mp member with leftMember | rightMember
    · exact leftContained value leftMember
    · exact rightContained value rightMember
  have bound := Nodup.nodup_length_le_of_mem appendedNodup carrierNodup
    appendedContained
  rw [Append.length_append] at bound
  exact (Nat.not_le_of_lt oversized) bound
end Purelib.Data.List

end
