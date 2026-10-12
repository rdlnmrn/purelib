module
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat.Fraction

section
public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data

/-- Find the greatest displayed rational value at or below a supplied cut.

Scan the finite list recursively, retaining none when no value qualifies and taking
the rational maximum whenever another qualifying value is found. -/
private def greatestAtMost : List Rational → Rational → Option Rational
  | [], _ => none
  | value :: remaining, cut =>
      match greatestAtMost remaining cut with
      | none => if value ≤ cut then some value else none
      | some current =>
          if value ≤ cut then some (max value current) else some current

/-- An empty predecessor result proves that no displayed rational value lies at or below
the cut. -/
private theorem greatestAtMost_none_no_member_le :
    ∀ (values : List Rational) (cut : Rational),
      greatestAtMost values cut = none →
        ∀ value, value ∈ values → ¬value ≤ cut
  | [], cut, empty, value, member => by nomatch member
  | head :: remaining, cut, empty, value, member => by
      unfold greatestAtMost at empty
      cases tailResult : greatestAtMost remaining cut with
      | none =>
          by_cases headLe : head ≤ cut
          · simp only [-eq_self, -iff_self, tailResult] at empty
            rw [if_pos headLe] at empty
            cases empty
          · simp only [-eq_self, -iff_self, tailResult] at empty
            rw [if_neg headLe] at empty
            rcases List.Membership.mem_cons.mp member with equal | tailMember
            · subst value
              exact headLe
            · exact greatestAtMost_none_no_member_le remaining cut
                tailResult value tailMember
      | some current =>
          by_cases headLe : head ≤ cut
          · simp only [-eq_self, -iff_self, tailResult] at empty
            rw [if_pos headLe] at empty
            cases empty
          · simp only [-eq_self, -iff_self, tailResult] at empty
            rw [if_neg headLe] at empty
            cases empty

/-- A successful predecessor result is a displayed value below the cut and bounds every
qualifying displayed value.

The membership, cut bound and greatest-value property all concern the exact retained
input list and returned rational value. -/
private theorem greatestAtMost_some_spec :
    ∀ (values : List Rational) (cut result : Rational),
      greatestAtMost values cut = some result →
        result ∈ values ∧ result ≤ cut ∧
          ∀ value, value ∈ values → value ≤ cut → value ≤ result
  | [], cut, result, selected => by cases selected
  | head :: remaining, cut, result, selected => by
      unfold greatestAtMost at selected
      cases tailResult : greatestAtMost remaining cut with
      | none =>
          by_cases headLe : head ≤ cut
          · simp only [-eq_self, -iff_self, tailResult] at selected
            rw [if_pos headLe] at selected
            have resultEqual : result = head := Option.some.inj selected.symm
            subst result
            refine ⟨List.mem_cons_self, headLe, ?_⟩
            intro value member valueLe
            rcases List.Membership.mem_cons.mp member with equal | tailMember
            · exact equal.le
            · exact (greatestAtMost_none_no_member_le remaining cut
                tailResult value tailMember valueLe).elim
          · simp only [-eq_self, -iff_self, tailResult] at selected
            rw [if_neg headLe] at selected
            cases selected
      | some current =>
          have tailSpec := greatestAtMost_some_spec remaining cut current
            tailResult
          by_cases headLe : head ≤ cut
          · simp only [-eq_self, -iff_self, tailResult] at selected
            rw [if_pos headLe] at selected
            have resultEqual : result = max head current :=
              Option.some.inj selected.symm
            subst result
            refine ⟨?_, Rat.Fraction.Order.Basic.max_le headLe tailSpec.2.1, ?_⟩
            · rcases Rat.Fraction.Order.Basic.le_total head current with headLeCurrent | currentLeHead
              · rw [Rat.Fraction.Order.Basic.max_eq_right headLeCurrent]
                exact List.mem_cons_of_mem head tailSpec.1
              · rw [Rat.Fraction.Order.Basic.max_eq_left currentLeHead]
                exact List.mem_cons_self
            · intro value member valueLe
              rcases List.Membership.mem_cons.mp member with equal | tailMember
              · subst value
                exact Rat.Fraction.Order.Basic.le_max_left _ _
              · exact (tailSpec.2.2 value tailMember valueLe).trans
                  (Rat.Fraction.Order.Basic.le_max_right _ _)
          · simp only [-eq_self, -iff_self, tailResult] at selected
            rw [if_neg headLe] at selected
            have resultEqual : result = current := Option.some.inj selected.symm
            subst result
            refine ⟨List.mem_cons_of_mem head tailSpec.1, tailSpec.2.1, ?_⟩
            intro value member valueLe
            rcases List.Membership.mem_cons.mp member with equal | tailMember
            · subst value
              exact (headLe valueLe).elim
            · exact tailSpec.2.2 value tailMember valueLe

/-- Compute the greatest displayed rational value at or below a supplied cut.

The finite scan returns none exactly when no entry qualifies. Repeated values remain
harmless because qualifying candidates are combined by rational maximum. -/
@[expose] def jumpPredecessor : List Rational → Rational → Option Rational
  | [], _ => none
  | value :: remaining, cut =>
      match jumpPredecessor remaining cut with
      | none => if value ≤ cut then some value else none
      | some current =>
          if value ≤ cut then some (max value current) else some current

/-- The public predecessor scan returns exactly the auxiliary certified scan's result. -/
private theorem jumpPredecessor_eq_greatestAtMost :
    ∀ (values : List Rational) (cut : Rational),
      jumpPredecessor values cut = greatestAtMost values cut := by
  intro values
  induction values with
  | nil => intro cut; rfl
  | cons value remaining ih =>
      intro cut
      simp only [-eq_self, -iff_self, jumpPredecessor, greatestAtMost, ih]
      rfl

/-- A missing predecessor excludes every displayed rational entry at or below the
supplied cut. -/
theorem jumpPredecessor_none_no_member_le
    (values : List Rational) (cut : Rational)
    (empty : jumpPredecessor values cut = none) :
    ∀ value, value ∈ values → ¬value ≤ cut := by
  rw [jumpPredecessor_eq_greatestAtMost values cut] at empty
  exact greatestAtMost_none_no_member_le values cut empty

/-- A returned predecessor belongs to the original list, lies below the cut and bounds
all qualifying entries.

The three retained properties certify the exact result of the finite scan without
introducing a supremum or any values outside the input list. -/
theorem jumpPredecessor_some_spec
    (values : List Rational) (cut result : Rational)
    (selected : jumpPredecessor values cut = some result) :
    result ∈ values ∧ result ≤ cut ∧
      ∀ value, value ∈ values → value ≤ cut → value ≤ result := by
  rw [jumpPredecessor_eq_greatestAtMost values cut] at selected
  exact greatestAtMost_some_spec values cut result selected

/-- Retain the displayed rational entries strictly below a supplied cut, in their
original order. -/
private def valuesStrictlyBelow
    (values : List Rational) (cut : Rational) : List Rational :=
  values.filter fun value => decide (value < cut)

/-- Membership in the strict-cut filter is exactly original membership together with the
strict cut bound. -/
private theorem mem_valuesStrictlyBelow_iff
    (values : List Rational) (cut value : Rational) :
    value ∈ valuesStrictlyBelow values cut ↔
      value ∈ values ∧ value < cut := by
  unfold valuesStrictlyBelow
  constructor
  · intro retained
    rcases List.Filter.mem_filter.mp retained with ⟨member, accepted⟩
    exact ⟨member, of_decide_eq_true accepted⟩
  · rintro ⟨member, ordered⟩
    exact List.Filter.mem_filter.mpr ⟨member, decide_eq_true ordered⟩
end Distribution

end Purelib.Measure

end
