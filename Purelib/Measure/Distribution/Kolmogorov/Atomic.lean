module
import Purelib.Data.List.Filter
import Purelib.Data.List.Rat.Predecessor
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Support
import Purelib.Measure.Weighted.Consolidation
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Consolidation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

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

open Purelib.Data

namespace Distribution

open Purelib.Data.Rat in
/-- A common support gap below an atom bounds the two atomic masses' separation by twice Kolmogorov distance.

Both original distributions must have no retained value strictly between the supplied lower cut and the exact atom
value. -/
private theorem atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
    (left right : Distribution Fraction.Rational)
    (item lower : Fraction.Rational) (lowerLt : lower < item)
    (leftGap : ∀ atom, atom ∈ left.atoms →
      atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item)
    (rightGap : ∀ atom, atom ∈ right.atoms →
      atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item) :
    Distance.rationalSeparation (left.atomMass item) (right.atomMass item) ≤
      2 * left.kolmogorovDistance right := by
  unfold atomMass atomEvent
  rw [left.probability_eqValue_eq_cumulative_sub_of_atom_gap lowerLt leftGap,
    right.probability_eqValue_eq_cumulative_sub_of_atom_gap lowerLt rightGap]
  calc
    Distance.rationalSeparation
        (left.cumulative item - left.cumulative lower)
        (right.cumulative item - right.cumulative lower) ≤
      Distance.rationalSeparation (left.cumulative item) (right.cumulative item) +
        Distance.rationalSeparation (left.cumulative lower) (right.cumulative lower) :=
      Distance.rationalSeparation_sub_le _ _ _ _
    _ ≤ left.kolmogorovDistance right +
        left.kolmogorovDistance right :=
      Fraction.Order.Arithmetic.add_le_add_direct
        (left.cumulative_separation_leKolmogorovDistance right item)
        (left.cumulative_separation_leKolmogorovDistance right lower)
    _ = 2 * left.kolmogorovDistance right := by ring1

open Purelib.Data.Rat in
open Purelib.Measure in
/-- The separation of any two corresponding atomic masses is at most twice the exact finite Kolmogorov distance.

The proof finds a predecessor in the retained combined support grid, including the case with no lower support value. -/
theorem atomMass_separation_le_two_mulKolmogorovDistance
    (left right : Distribution Fraction.Rational) (item : Fraction.Rational) :
    Distance.rationalSeparation (left.atomMass item) (right.atomMass item) ≤
      2 * left.kolmogorovDistance right := by
  let values := cumulativeSupportGrid left right
  let below := values.filter fun value => decide (value < item)
  have mem_below_iff (value : Fraction.Rational) :
      value ∈ below ↔ value ∈ values ∧ value < item := by
    constructor
    · intro member
      have accepted := (List.Filter.mem_filter (values := values)).mp member
      exact ⟨accepted.1, of_decide_eq_true accepted.2⟩
    · rintro ⟨member, belowItem⟩
      exact (List.Filter.mem_filter (values := values)).mpr ⟨member, decide_eq_true belowItem⟩
  cases selected : Distribution.jumpPredecessor below item with
  | none =>
      have noValueBelow : ∀ value, value ∈ values → ¬value < item := by
        intro value member valueLt
        have belowMember : value ∈ below :=
          (mem_below_iff value).2
            ⟨member, valueLt⟩
        exact Distribution.jumpPredecessor_none_no_member_le below item selected value
          belowMember valueLt.le
      have lowerLt : item - 1 < item := by
        calc
          item - 1 < item - 0 :=
            Fraction.Order.Arithmetic.sub_lt_sub_left_direct
              (a := 0) (b := 1) (by decide) item
          _ = item := by ring1
      have gap : ∀ (distribution : Distribution Fraction.Rational),
          (∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) →
          ∀ atom, atom ∈ distribution.atoms →
            atom.item ≤ item - 1 ∨ atom.item = item ∨ item < atom.item := by
        intro distribution covers atom member
        have notBelow := noValueBelow atom.item (covers atom member)
        rcases lt_trichotomy item atom.item with above | equal | belowItem
        · exact Or.inr (Or.inr above)
        · exact Or.inr (Or.inl equal.symm)
        · exact (notBelow belowItem).elim
      exact
        atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
          left right item (item - 1) lowerLt
          (gap left (Distribution.left_item_mem_cumulativeSupportGrid left right))
          (gap right (Distribution.right_item_mem_cumulativeSupportGrid left right))
  | some result =>
      have spec := Distribution.jumpPredecessor_some_spec below item result selected
      have resultBelow : result < item :=
        (mem_below_iff result).1 spec.1 |>.2
      have greatestBelow : ∀ value, value ∈ values → value < item →
          value ≤ result := by
        intro value member valueLt
        exact spec.2.2 value
          ((mem_below_iff value).2
            ⟨member, valueLt⟩)
          valueLt.le
      have gap : ∀ (distribution : Distribution Fraction.Rational),
          (∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) →
          ∀ atom, atom ∈ distribution.atoms →
            atom.item ≤ result ∨ atom.item = item ∨ item < atom.item := by
        intro distribution covers atom member
        rcases lt_trichotomy atom.item item with belowItem | equal | above
        · exact Or.inl (greatestBelow atom.item (covers atom member)
            belowItem)
        · exact Or.inr (Or.inl equal)
        · exact Or.inr (Or.inr above)
      exact
        atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
          left right item result resultBelow
          (gap left (Distribution.left_item_mem_cumulativeSupportGrid left right))
          (gap right (Distribution.right_item_mem_cumulativeSupportGrid left right))
end Distribution

end Purelib.Measure

end
