module
import Purelib.Data.Bool.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.AlmostEverywhere
public import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite rational cumulative contents

For a rational-valued finite distribution, cumulative probabilities are
exact evaluations of executable order tests.  Monotonicity and interval-mass
identities are finite Boolean-event calculations.  No continuity, supremum,
or real-valued distribution function is introduced.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data

section
open Purelib.Data.Rat
/-- Read the retained rational distribution's probability of values at most the supplied threshold. -/
@[expose] def cumulative (distribution : Distribution Fraction.Rational)
    (threshold : Fraction.Rational) : Fraction.Rational :=
  distribution.probability (atMostEvent threshold)

/-- The cumulative probability at every rational cut is nonnegative. -/
theorem cumulative_nonneg (distribution : Distribution Fraction.Rational)
    (threshold : Fraction.Rational) :
    0 ≤ distribution.cumulative threshold :=
  distribution.probability_nonneg _

/-- The cumulative probability at every rational cut is at most one. -/
theorem cumulative_le_one (distribution : Distribution Fraction.Rational)
    (threshold : Fraction.Rational) :
    distribution.cumulative threshold ≤ 1 :=
  distribution.probability_le_one _

/-- Increasing a rational cut cannot decrease the retained distribution's cumulative probability. -/
theorem cumulative_mono (distribution : Distribution Fraction.Rational)
    {lower upper : Fraction.Rational} (order : lower ≤ upper) :
    distribution.cumulative lower ≤ distribution.cumulative upper := by
  apply eventWeight_mono
  intro atom member selected
  have atomLeLower : atom.item ≤ lower := of_decide_eq_true selected
  exact decide_eq_true (atomLeLower.trans order)

/-- A cut strictly below every retained payload has cumulative probability zero. -/
theorem cumulative_eq_zero_of_cut_lt_all_atoms
    (distribution : Distribution Fraction.Rational) (cut : Fraction.Rational)
    (below : ∀ atom, atom ∈ distribution.atoms → cut < atom.item) :
    distribution.cumulative cut = 0 := by
  unfold cumulative
  calc
    distribution.probability (atMostEvent cut) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      have notAtMost : ¬atom.item ≤ cut := (below atom member).2
      simp only [-eq_self, -iff_self, atMostEvent, decide_eq_false notAtMost]
      rfl
    _ = 0 := distribution.probability_false

/-- A cut at least every retained payload has cumulative probability one. -/
theorem cumulative_eq_one_of_all_atoms_le_cut
    (distribution : Distribution Fraction.Rational) (cut : Fraction.Rational)
    (above : ∀ atom, atom ∈ distribution.atoms → atom.item ≤ cut) :
    distribution.cumulative cut = 1 := by
  unfold cumulative
  calc
    distribution.probability (atMostEvent cut) =
        distribution.probability (fun _ => true) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      simp only [-eq_self, -iff_self, atMostEvent, decide_eq_true (above atom member)]
      rfl
    _ = 1 := distribution.probability_true

/-- Two ordered cuts with no retained payload between them have equal cumulative probability. -/
theorem cumulative_eq_of_atom_gap
    (distribution : Distribution Fraction.Rational)
    {lower upper : Fraction.Rational} (order : lower ≤ upper)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ upper < atom.item) :
    distribution.cumulative lower = distribution.cumulative upper := by
  unfold cumulative
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold atMostEvent
  rcases gap atom member with below | above
  · have upperSelected : atom.item ≤ upper := below.trans order
    simp only [-eq_self, -iff_self, decide_eq_true below, decide_eq_true upperSelected]
    rfl
  · have lowerAbove : lower < atom.item := order.trans_lt above
    have notLower : ¬atom.item ≤ lower := lowerAbove.2
    have notUpper : ¬atom.item ≤ upper := above.2
    simp only [-eq_self, -iff_self, decide_eq_false notLower, decide_eq_false notUpper]
    rfl

/-- A lower cut and the open-closed interval starting at that cut are disjoint on the retained occurrences. -/
private theorem atMost_disjoint_interval
    (distribution : Distribution Fraction.Rational) (lower upper : Fraction.Rational) :
    DisjointOn distribution.atoms (atMostEvent lower)
      (openClosedIntervalEvent lower upper) := by
  intro atom member selected
  have atomLeLower : atom.item ≤ lower := of_decide_eq_true selected.1
  have lowerLtAtom : lower < atom.item := by
    have intervalTrue := (Bool.Decide.and_true_iff _ _).mp selected.2
    exact of_decide_eq_true intervalTrue.1
  exact (lowerLtAtom.2 atomLeLower).elim

open Purelib.Measure in
/-- An ordered open-closed interval has probability equal to the difference of its endpoint cumulative values. -/
theorem probability_openClosedInterval
    (distribution : Distribution Fraction.Rational)
    {lower upper : Fraction.Rational} (order : lower ≤ upper) :
    distribution.probability (openClosedIntervalEvent lower upper) =
      distribution.cumulative upper - distribution.cumulative lower := by
  have additive := distribution.probability_union_of_disjoint
    (atMost_disjoint_interval distribution lower upper)
  have unionEqual : distribution.probability
        (unionEvent (atMostEvent lower)
          (openClosedIntervalEvent lower upper)) =
      distribution.probability (atMostEvent upper) :=
    distribution.probability_congr _ _ (Distribution.atMost_union_interval order)
  rw [unionEqual] at additive
  change distribution.probability (openClosedIntervalEvent lower upper) =
    distribution.probability (atMostEvent upper) -
      distribution.probability (atMostEvent lower)
  rw [additive]
  ring1

/-- An ordered interval containing no retained payload has probability zero. -/
theorem probability_openClosedInterval_eq_zero_of_atom_gap
    (distribution : Distribution Fraction.Rational)
    {lower upper : Fraction.Rational} (order : lower ≤ upper)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ upper < atom.item) :
    distribution.probability (openClosedIntervalEvent lower upper) = 0 := by
  rw [distribution.probability_openClosedInterval order,
    ← distribution.cumulative_eq_of_atom_gap order gap]
  ring1

/-- An isolated payload's equality-event probability is the cumulative jump from the retained lower cut.

Every retained payload lies below the lower cut, equals the selected value, or lies strictly above it. The lower cut is
strictly below that value, so the intervening cumulative difference selects exactly its occurrences. -/
theorem probability_eqValue_eq_cumulative_sub_of_atom_gap
    (distribution : Distribution Fraction.Rational)
    {lower value : Fraction.Rational} (lowerLtValue : lower < value)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ atom.item = value ∨ value < atom.item) :
    distribution.probability (fun candidate => decide (candidate = value)) =
      distribution.cumulative value - distribution.cumulative lower := by
  calc
    distribution.probability (fun candidate => decide (candidate = value)) =
        distribution.probability
          (openClosedIntervalEvent lower value) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      rcases gap atom member with below | equalOrAbove
      · have notEqual : atom.item ≠ value := by
          intro equal
          rw [equal] at below
          exact (lowerLtValue.2 below).elim
        have notAboveLower : ¬lower < atom.item := by
          intro aboveLower
          exact (aboveLower.2 below).elim
        simp only [-eq_self, -iff_self, openClosedIntervalEvent, decide_eq_false notEqual, decide_eq_false
          notAboveLower,
           Bool.false_and]
        rfl
      · rcases equalOrAbove with equal | above
        · rw [equal]
          unfold openClosedIntervalEvent
          simp only [-eq_self, -iff_self, decide_eq_true lowerLtValue, decide_eq_true (Fraction.Order.Basic.le_refl
            value), decide_eq_true (rfl : value = value), Bool.true_and]
          rfl
        · have notEqual : atom.item ≠ value := by
            intro equal
            rw [equal] at above
            exact (lt_irrefl _ above).elim
          have notAtMost : ¬atom.item ≤ value := above.2
          simp only [-eq_self, -iff_self, openClosedIntervalEvent, decide_eq_false notEqual, decide_eq_false notAtMost,
             Bool.and_false]
          rfl
    _ = distribution.cumulative value - distribution.cumulative lower :=
      distribution.probability_openClosedInterval lowerLtValue.le

end

end Distribution

end Purelib.Measure

end
