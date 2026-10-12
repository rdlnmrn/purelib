module

public import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
public import Purelib.Data.List.Rat.Predecessor
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Cumulative.Grid
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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
/-- List the payloads of the exact retained distribution, preserving order and repeated occurrences. -/
@[expose] def atomPayloadGrid (distribution : Distribution Fraction.Rational) :
    List Fraction.Rational :=
  distribution.atoms.map fun atom => atom.item

open Purelib.Data.List in
open Purelib.Data.Rat in
/-- Every retained occurrence's payload belongs to the original payload grid. -/
theorem atom_item_mem_atomPayloadGrid
    (distribution : Distribution Fraction.Rational)
    (atom : Weighted Fraction.Rational) (member : atom ∈ distribution.atoms) :
    atom.item ∈ distribution.atomPayloadGrid :=
  Map.mem_map.mpr ⟨atom, member, rfl⟩

section
open Purelib.Data.Rat
/-- Concatenate the two original payload grids to cover all retained occurrences of both laws. -/
@[expose] def cumulativeSupportGrid (left right : Distribution Fraction.Rational) :
    List Fraction.Rational :=
  left.atomPayloadGrid ++ right.atomPayloadGrid

/-- Every left-law occurrence's payload belongs to the combined cumulative grid. -/
theorem left_item_mem_cumulativeSupportGrid
    (left right : Distribution Fraction.Rational)
    (atom : Weighted Fraction.Rational) (member : atom ∈ left.atoms) :
    atom.item ∈ cumulativeSupportGrid left right :=
  List.Membership.mem_append.mpr (Or.inl
    (left.atom_item_mem_atomPayloadGrid atom member))

/-- Every right-law occurrence's payload belongs to the combined cumulative grid. -/
theorem right_item_mem_cumulativeSupportGrid
    (left right : Distribution Fraction.Rational)
    (atom : Weighted Fraction.Rational) (member : atom ∈ right.atoms) :
    atom.item ∈ cumulativeSupportGrid left right :=
  List.Membership.mem_append.mpr (Or.inr
    (right.atom_item_mem_atomPayloadGrid atom member))

end

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a strict predecessor cut isolating the specified payload's cumulative jump in the exact distribution.

Every original occurrence lies at or below the retained lower cut, equals the specified payload, or lies strictly above
that payload. -/
structure CumulativeJumpCertificate
    (distribution : Distribution Fraction.Rational) (item : Fraction.Rational) where
  /-- The retained lower cut isolating the specified payload's jump. -/ lower : Fraction.Rational
  /-- The retained lower cut is strictly below the specified payload. -/ lower_lt : lower < item
  /-- Every original occurrence lies below the cut, at the specified payload, or strictly above that payload. -/
    isolates : ∀ atom, atom ∈ distribution.atoms →
    atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item

constructive_injectivity CumulativeJumpCertificate

section
open Purelib.Data.Rat
/-- Find an isolating lower cut by scanning original payloads strictly below the specified point.

Use their greatest retained predecessor when available; otherwise use the specified point minus one. The returned
certificate covers the exact original atom list. -/
@[expose] def cumulativeJumpCertificate
    (distribution : Distribution Fraction.Rational) (item : Fraction.Rational) :
    CumulativeJumpCertificate distribution item := by
  let values := distribution.atomPayloadGrid
  let below := values.filter fun value => decide (value < item)
  have mem_below_iff (value : Fraction.Rational) :
      value ∈ below ↔ value ∈ values ∧ value < item := by
    constructor
    · intro member
      have selected := (List.Filter.mem_filter (values := values)).mp member
      exact ⟨selected.1, of_decide_eq_true selected.2⟩
    · rintro ⟨member, belowItem⟩
      exact (List.Filter.mem_filter (values := values)).mpr ⟨member, decide_eq_true belowItem⟩
  cases selected : jumpPredecessor below item with
  | none =>
      refine
        { lower := item - 1
          lower_lt := ?_
          isolates := ?_ }
      · calc
          item - 1 < item - 0 :=
            Fraction.Order.Arithmetic.sub_lt_sub_left_direct
              (a := 0) (b := 1) (by decide) item
          _ = item := by
            have zeroNeg : -(0 : Fraction.Rational) = 0 :=
              SubtractionMonoid.neg_eq_of_add 0 0 (AddZeroClass.add_zero 0)
            calc
              item - 0 = item + -0 := SubNegMonoid.sub_eq_add_neg item 0
              _ = item + 0 := congrArg (fun value => item + value) zeroNeg
              _ = item := AddZeroClass.add_zero item
      · intro atom member
        have atomInValues : atom.item ∈ values :=
          distribution.atom_item_mem_atomPayloadGrid atom member
        have notBelow : ¬atom.item < item := by
          intro atomBelow
          have belowMember : atom.item ∈ below :=
            (mem_below_iff atom.item).2
              ⟨atomInValues, atomBelow⟩
          exact jumpPredecessor_none_no_member_le below item selected atom.item
            belowMember atomBelow.le
        rcases lt_trichotomy item atom.item with above | equal | belowItem
        · exact Or.inr (Or.inr above)
        · exact Or.inr (Or.inl equal.symm)
        · exact (notBelow belowItem).elim
  | some result =>
      have spec := jumpPredecessor_some_spec below item result selected
      have resultBelow : result < item :=
        (mem_below_iff result).1 spec.1 |>.2
      refine
        { lower := result
          lower_lt := resultBelow
          isolates := ?_ }
      intro atom member
      rcases lt_trichotomy atom.item item with atomBelow | equal | above
      · apply Or.inl
        apply spec.2.2 atom.item
        · exact (mem_below_iff atom.item).2
            ⟨distribution.atom_item_mem_atomPayloadGrid atom member,
              atomBelow⟩
        · exact atomBelow.le
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr above)

/-- Singleton mass equals the cumulative jump from its retained isolating lower cut to the specified payload. -/
theorem atomMass_eq_cumulative_sub_jumpCertificate
    (distribution : Distribution Fraction.Rational) (item : Fraction.Rational) :
    distribution.atomMass item =
      distribution.cumulative item -
        distribution.cumulative
          (distribution.cumulativeJumpCertificate item).lower := by
  unfold atomMass
  exact distribution.probability_eqValue_eq_cumulative_sub_of_atom_gap
    (distribution.cumulativeJumpCertificate item).lower_lt
    (distribution.cumulativeJumpCertificate item).isolates

end

section
open Purelib.Data.Rat
open Purelib.Measure
/-- On a list covering all retained payloads, the greatest value below a cut has the same cumulative probability as that
cut. -/
private theorem cumulative_eq_at_greatestAtMost
    (distribution : Distribution Fraction.Rational)
    (values : List Fraction.Rational) (cut result : Fraction.Rational)
    (selected : Distribution.jumpPredecessor values cut = some result)
    (covers : ∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) :
    distribution.cumulative cut = distribution.cumulative result := by
  let spec := Distribution.jumpPredecessor_some_spec values cut result selected
  unfold cumulative
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold atMostEvent
  by_cases atomLeCut : atom.item ≤ cut
  · have atomLeResult := spec.2.2 atom.item (covers atom member) atomLeCut
    exact (decide_eq_true atomLeCut).trans (decide_eq_true atomLeResult).symm
  · have notLeResult : ¬atom.item ≤ result := by
      intro atomLeResult
      exact atomLeCut (atomLeResult.trans spec.2.1)
    exact (decide_eq_false atomLeCut).trans (decide_eq_false notLeResult).symm

/-- A cut with no predecessor in a list covering all retained payloads has cumulative probability zero. -/
private theorem cumulative_eq_zero_of_greatestAtMost_none
    (distribution : Distribution Fraction.Rational)
    (values : List Fraction.Rational) (cut : Fraction.Rational)
    (empty : Distribution.jumpPredecessor values cut = none)
    (covers : ∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) :
    distribution.cumulative cut = 0 := by
  unfold cumulative
  calc
    distribution.probability (atMostEvent cut) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      have notLe := Distribution.jumpPredecessor_none_no_member_le values cut empty atom.item
        (covers atom member)
      unfold atMostEvent
      exact decide_eq_false notLe
    _ = 0 := distribution.probability_false

/-- A threshold grid covering both retained supports controls cumulative separation at every rational cut. -/
theorem cumulative_separation_le_cumulativeGridDistance_of_support_covered
    (left right : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (leftCovered : ∀ atom, atom ∈ left.atoms → atom.item ∈ thresholds)
    (rightCovered : ∀ atom, atom ∈ right.atoms → atom.item ∈ thresholds)
    (cut : Fraction.Rational) :
    Distance.rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.cumulativeGridDistance right thresholds := by
  cases selected : Distribution.jumpPredecessor thresholds cut with
  | none =>
      have leftZero := cumulative_eq_zero_of_greatestAtMost_none left
        thresholds cut selected leftCovered
      have rightZero := cumulative_eq_zero_of_greatestAtMost_none right
        thresholds cut selected rightCovered
      rw [leftZero, rightZero]
      exact (Distance.rationalSeparation_eq_zero_iff 0 0).mpr rfl |>.le.trans
        (left.cumulativeGridDistance_nonnegative right thresholds)
  | some result =>
      have spec := Distribution.jumpPredecessor_some_spec thresholds cut result selected
      have leftEqual := cumulative_eq_at_greatestAtMost left thresholds cut
        result selected leftCovered
      have rightEqual := cumulative_eq_at_greatestAtMost right thresholds cut
        result selected rightCovered
      rw [leftEqual, rightEqual]
      exact left.cumulative_separation_le_cumulativeGridDistance right result
        spec.1

end

open Purelib.Data.Rat in
/-- The combined original payload grid controls cumulative separation at every rational cut. -/
theorem cumulative_separation_le_cumulativeSupportGridDistance
    (left right : Distribution Fraction.Rational) (cut : Fraction.Rational) :
    Distance.rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.cumulativeGridDistance right
        (cumulativeSupportGrid left right) := by
  exact left.cumulative_separation_le_cumulativeGridDistance_of_support_covered
    right (cumulativeSupportGrid left right)
      (left_item_mem_cumulativeSupportGrid left right)
      (right_item_mem_cumulativeSupportGrid left right) cut
end Distribution

end Purelib.Measure

end
