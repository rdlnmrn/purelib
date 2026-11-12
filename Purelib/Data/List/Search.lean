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

public section

/-- A retained first accepted occurrence, including its original position, complete entry and rejected earlier keys.

The original list is an index. The entry is the identical stored list value,
not a reconstructed owner or a value selected from a membership proof.
-/
@[expose] def Occurrence (accept : Alpha → Prop) (values : List Alpha) : Type u :=
  (index : Fin values.length) ×
  { entry : Alpha // entry = values[index.val]'index.isLt ∧ accept entry ∧
    ∀ earlier : Fin values.length, earlier.val < index.val → ¬ accept (values[earlier.val]'earlier.isLt) }

namespace Occurrence

variable {accept : Alpha → Prop} {values : List Alpha} (selected : Occurrence accept values)

/-- Read the actual bounded position selected by the original finite scan. -/
@[expose] def index : Fin values.length := selected.1

/-- Read the same complete original selected entry without rebuilding any of its fields. -/
@[expose] def entry : Alpha := selected.2.val

/-- The selected entry is the identical original list value at its retained position. -/
theorem entry_eq : selected.entry = values[selected.index.val]'selected.index.isLt := selected.2.property.1

/-- The complete selected entry belongs to its SAME original source list. -/
theorem member : selected.entry ∈ values :=
  Eq.mp (congrArg (fun entry => entry ∈ values) selected.entry_eq.symm) (List.getElem_mem _)

/-- The actual selected entry satisfies the original predicate. -/
theorem accepted : accept selected.entry := selected.2.property.2.1

/-- Every earlier original position fails the same predicate, even when later entries repeat the key. -/
theorem earlier (index : Fin values.length) (before : index.val < selected.index.val) :
    ¬ accept (values[index.val]'index.isLt) := selected.2.property.2.2 index before

end Occurrence

/-- Retain an accepted actual head with position zero and no preceding occurrence. -/
private def headOccurrence (accept : Alpha → Prop) (head : Alpha) (tail : List Alpha) (kept : accept head) :
    Occurrence accept (head :: tail) :=
  ⟨0, ⟨head, rfl, kept, fun index before => False.elim (Nat.not_lt_zero index.val before)⟩⟩

/-- Shift the same selected tail occurrence past one rejected original head. -/
private def prependOccurrence {accept : Alpha → Prop} {tail : List Alpha}
    (head : Alpha) (rejected : ¬ accept head) (selected : Occurrence accept tail) :
    Occurrence accept (head :: tail) :=
  ⟨selected.index.succ, ⟨selected.entry, selected.entry_eq, selected.accepted, by
    intro earlier before
    cases earlier with
    | mk value bounded =>
      cases value with
      | zero => exact rejected
      | succ value =>
        exact selected.earlier ⟨value, Nat.lt_of_succ_lt_succ bounded⟩
          (Nat.lt_of_succ_lt_succ before)⟩⟩

/-- Scan once for the first accepted original occurrence and retain its exact position and whole entry.

The supplied decision procedure is run once on each visited head, in original
list order. Acceptance returns immediately; rejection preserves the same
recursive tail result and shifts only its bounded position. No observer or
entry-producing operation is invoked by the scan.
-/
def firstOccurrence (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry)) :
    (values : List Alpha) → Option (Occurrence accept values)
  | [] => none
  | head :: tail =>
      match decisions head with
      | .isTrue kept => some (headOccurrence accept head tail kept)
      | .isFalse rejected => (firstOccurrence accept decisions tail).map (prependOccurrence head rejected)

/-- An original failed occurrence scan rejects every actual source entry. -/
private theorem firstOccurrence_rejects (accept : Alpha → Prop)
    (decisions : (entry : Alpha) → Decidable (accept entry)) :
    (values : List Alpha) → firstOccurrence accept decisions values = none →
      ∀ entry ∈ values, ¬ accept entry
  | [], _, _, member => by nomatch member
  | head :: tail, failed, entry, member => by
      cases choice : decisions head with
      | isTrue kept =>
          have impossible := failed
          rewrite [firstOccurrence, choice] at impossible
          nomatch impossible
      | isFalse rejected =>
          have tailFailed : firstOccurrence accept decisions tail = none := by
            cases selected : firstOccurrence accept decisions tail with
            | none => rfl
            | some retained =>
                have impossible := failed
                rewrite [firstOccurrence, choice, selected] at impossible
                nomatch impossible
          rcases Membership.mem_cons.mp member with equal | member
          · exact fun kept => rejected (Eq.mp (congrArg accept equal) kept)
          · exact firstOccurrence_rejects accept decisions tail tailFailed entry member

/-- Retain the whole original first accepted occurrence when genuine finite acceptance is already proved.

The original scan runs once. Its entire selected value and original whole
result equation are retained. The existence proof only rules out the none
branch; it is never eliminated to choose runtime data.
-/
def firstAccepted (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry))
    (values : List Alpha) (accepted : ∃ entry ∈ values, accept entry) :
    {selected : Occurrence accept values // firstOccurrence accept decisions values = some selected} :=
  match result : firstOccurrence accept decisions values with
  | some selected => ⟨selected, rfl⟩
  | none => False.elim (by
      obtain ⟨entry, member, kept⟩ := accepted
      exact firstOccurrence_rejects accept decisions values result entry member kept)

/-- Forget only the occurrence certificates of the same finite scan, preserving its complete selected value. -/
def firstValue (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry))
    (values : List Alpha) : Option Alpha :=
  (firstOccurrence accept decisions values).map Occurrence.entry

/-- The original value view forgets only the same finite scan's retained positional evidence. -/
theorem firstValue_eq_occurrence (accept : Alpha → Prop)
    (decisions : (entry : Alpha) → Decidable (accept entry)) (values : List Alpha) :
    firstValue accept decisions values = (firstOccurrence accept decisions values).map Occurrence.entry := by
  unfold firstValue
  rfl

/-- An empty original list has no accepted value or retained occurrence. -/
theorem firstValue_nil (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry)) :
    firstValue accept decisions [] = none := by
  unfold firstValue firstOccurrence
  rfl

/-- An accepted head returns its identical original value without visiting the retained tail. -/
theorem firstValue_cons_pos (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry))
    (head : Alpha) (tail : List Alpha) (kept : accept head) :
    firstValue accept decisions (head :: tail) = some head := by
  unfold firstValue
  rewrite [firstOccurrence]
  cases decisions head with
  | isTrue _ => rfl
  | isFalse rejected => exact False.elim (rejected kept)

/-- A rejected head leaves the same original finite value lookup on the unchanged tail. -/
theorem firstValue_cons_neg (accept : Alpha → Prop) (decisions : (entry : Alpha) → Decidable (accept entry))
    (head : Alpha) (tail : List Alpha) (rejected : ¬ accept head) :
    firstValue accept decisions (head :: tail) = firstValue accept decisions tail := by
  unfold firstValue
  rewrite [firstOccurrence]
  cases decisions head with
  | isTrue kept => exact False.elim (rejected kept)
  | isFalse _ =>
      cases firstOccurrence accept decisions tail <;> rfl

end

end Purelib.Data.List.Search
