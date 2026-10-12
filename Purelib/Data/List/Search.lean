module

import Mathlib.Tactic.TypeStar
import Purelib.Data.List.Membership
public import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Certificates for finite Boolean searches

The original list search retains its predicate, source spine and selected value.
Structural certificates characterize success and rejection and recover both
membership and predicate acceptance of the exact returned target.
-/

namespace Purelib.Data.List.Search

universe u

open Purelib.Data.Rat

variable {Alpha : Type u}

/-- A Boolean finite-list search succeeds when a displayed member satisfies its
predicate.

Structural recursion retains the same predicate and original list spine. Head
and tail membership constructors transfer the supplied occurrence, while a
rejected head is ruled out by its actual Boolean value. -/
public theorem find?_isSome {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      (values.find? predicate).isSome ↔
        ∃ value, value ∈ values ∧ predicate value
  | [] => by
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      cases selected : predicate value with
      | false =>
          rw [List.find?_cons, selected]
          constructor
          · intro found
            rcases (find?_isSome (values := values)).mp found with
              ⟨source, sourceMember, accepted⟩
            exact ⟨source, List.Mem.tail value sourceMember, accepted⟩
          · rintro ⟨source, sourceMember, accepted⟩
            cases sourceMember with
            | head =>
                rewrite [selected] at accepted
                exact Bool.noConfusion accepted
            | tail _ tailMember =>
                exact (find?_isSome (values := values)).mpr
                  ⟨source, tailMember, accepted⟩
      | true =>
          rw [List.find?_cons, selected]
          constructor
          · intro _
            exact ⟨value, List.mem_cons_self, selected⟩
          · intro _
            rfl

/-- A Boolean finite-list search returns none when every displayed member is rejected.

Structural recursion retains the original Boolean predicate and list spine.
The head and tail membership constructors propagate rejection in both
logical directions without proposition-equality rewriting. -/
public theorem find?_eq_none {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      values.find? predicate = none ↔
        ∀ value ∈ values, predicate value = false
  | [] => by
      constructor
      · intro _ value impossible
        nomatch impossible
      · intro _
        rfl
  | head :: tail => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted]
          constructor
          · intro found value member
            cases member with
            | head => exact accepted
            | tail _ tailMember => exact find?_eq_none.mp found value tailMember
          · intro rejected
            exact find?_eq_none.mpr
              (fun value member => rejected value (List.Mem.tail head member))
      | true =>
          rw [List.find?_cons, accepted]
          constructor
          · intro impossible
            nomatch impossible
          · intro rejected
            have impossible := rejected head (List.Mem.head tail)
            rw [accepted] at impossible
            exact Bool.noConfusion impossible

/-- A returned search value retains its original occurrence and Boolean acceptance.

Structural recursion follows the same list search and predicate. A rejected
head retains the recursive tail certificate; an accepted head identifies the
returned target and supplies its displayed membership constructor. -/
private theorem find?_eq_some_certificate {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha}, values.find? predicate = some target →
      target ∈ values ∧ predicate target = true
  | [], impossible => by
      nomatch impossible
  | head :: tail, found => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted] at found
          obtain ⟨member, passed⟩ := find?_eq_some_certificate found
          exact ⟨List.Mem.tail head member, passed⟩
      | true =>
          rw [List.find?_cons, accepted] at found
          injection found with equal
          cases equal
          exact ⟨List.Mem.head tail, accepted⟩

/-- Retain Boolean predicate acceptance of the value returned by finite-list search.

The supplied result equality refers to the same original list and predicate.
Its structural search certificate supplies acceptance of that exact target. -/
public theorem find?_eq_some_accepts_certificate {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} {values : List Alpha}
    (found : values.find? predicate = some target) : predicate target = true :=
  (find?_eq_some_certificate found).2

/-- Retain original-list membership of the value returned by finite-list search.

The supplied result equality identifies the returned target without replacing
its source list. The structural search certificate retains its actual occurrence. -/
public theorem find?_eq_some_mem_certificate {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} {values : List Alpha}
    (found : values.find? predicate = some target) : target ∈ values :=
  (find?_eq_some_certificate found).1

/-- A successful Boolean list test retains an accepted source occurrence.

The witness lies in the same ordered list and satisfies the retained predicate.
Structural head and tail cases preserve the actual occurrence certificate. -/
public theorem any_witness {Label : Type u} (keep : Label → Bool) :
    (labels : List Label) → labels.any keep = true → ∃ label ∈ labels, keep label = true
  | [], found => Bool.noConfusion found
  | head :: tail, found => by
      cases equal : keep head
      · change (keep head || tail.any keep) = true at found
        rw [equal, Bool.false_or] at found
        obtain ⟨label, member, kept⟩ := any_witness keep tail found
        exact ⟨label, List.Mem.tail head member, kept⟩
      · exact ⟨head, List.Mem.head tail, equal⟩

/-- A Boolean list search succeeds exactly when a retained member satisfies its predicate.

Both implications retain the original list and Boolean predicate. Structural head
and tail cases produce or consume the displayed membership and acceptance witness. -/
public theorem any_iff {Item : Type} (keep : Item → Bool) (entries : List Item) :
    entries.any keep = true ↔ ∃ entry ∈ entries, keep entry = true := by
  induction entries with
  | nil =>
      constructor
      · intro impossible; exact (Bool.noConfusion impossible)
      · rintro ⟨entry, member, _⟩; exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      cases equal : keep head with
      | false =>
          constructor
          · intro present
            have remaining : tail.any keep = true := by
              simpa only [-eq_self, -iff_self, List.any_cons, equal, Bool.false_or] using present
            obtain ⟨entry, member, kept⟩ := ih.mp remaining
            exact ⟨entry, List.mem_cons_of_mem _ member, kept⟩
          · rintro ⟨entry, member, kept⟩
            rcases Membership.mem_cons.mp member with same | member
            · cases same
              exact Bool.noConfusion (equal.symm.trans kept)
            · rw [List.any_cons, equal, Bool.false_or]
              exact ih.mpr ⟨entry, member, kept⟩
      | true =>
          constructor
          · intro _; exact ⟨head, List.mem_cons_self, equal⟩
          · intro _; rw [List.any_cons, equal, Bool.true_or]

/-- A finite rational list with a failed universal zero test contains a nonzero evaluation.

The witness is found by structural case analysis on the original list. -/
public theorem exists_member_ne_zero_of_not_all_zero
    (values : List Fraction.Rational) (evaluation : Fraction.Rational → Fraction.Rational)
    (notAllZero : ¬ ∀ point ∈ values, evaluation point = 0) :
    ∃ point ∈ values, evaluation point ≠ 0 := by
  induction values with
  | nil =>
      exact (notAllZero (fun point member => by
        nomatch member)).elim
  | cons first remaining inductionHypothesis =>
      by_cases firstZero : evaluation first = 0
      · have tailNotAllZero :
            ¬ ∀ point ∈ remaining, evaluation point = 0 := by
          intro tailAllZero
          apply notAllZero
          intro point member
          rcases Membership.mem_cons.mp member with equal | later
          · cases equal
            exact firstZero
          · exact tailAllZero point later
        obtain ⟨point, member, nonzero⟩ := inductionHypothesis tailNotAllZero
        exact ⟨point, List.Mem.tail first member, nonzero⟩
      · exact ⟨first, List.Mem.head remaining, firstZero⟩

end Purelib.Data.List.Search
