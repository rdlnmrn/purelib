import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Convolution
import FiniteMeasure.Mixture
import FiniteMeasure.ZeroWeight

/-!
# Finite rational cumulative contents

For a rational-valued finite distribution, cumulative probabilities are
exact evaluations of executable order tests.  Monotonicity and interval-mass
identities are finite Boolean-event calculations.  No continuity, supremum,
or real-valued distribution function is introduced.
-/

namespace FiniteMeasure

/-- Executable rational lower-ray event. -/
def atMostEvent (threshold : Coordinate) : Coordinate → Bool :=
  fun value => decide (value ≤ threshold)

/-- Executable rational half-open interval event `(lower, upper]`. -/
def openClosedIntervalEvent (lower upper : Coordinate) : Coordinate → Bool :=
  fun value => decide (lower < value) && decide (value ≤ upper)

namespace Distribution

/-- Exact finite cumulative rational probability. -/
def cumulative (distribution : Distribution Coordinate)
    (threshold : Coordinate) : Coordinate :=
  distribution.probability (atMostEvent threshold)

theorem cumulative_nonneg (distribution : Distribution Coordinate)
    (threshold : Coordinate) :
    0 ≤ distribution.cumulative threshold :=
  distribution.probability_nonneg _

theorem cumulative_le_one (distribution : Distribution Coordinate)
    (threshold : Coordinate) :
    distribution.cumulative threshold ≤ 1 :=
  distribution.probability_le_one _

/-- Exact finite cumulative monotonicity. -/
theorem cumulative_mono (distribution : Distribution Coordinate)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    distribution.cumulative lower ≤ distribution.cumulative upper := by
  apply eventWeight_mono
  intro atom member selected
  have atomLeLower : atom.item ≤ lower := of_decide_eq_true selected
  exact decide_eq_true_eq.mpr (atomLeLower.trans order)

/-- A rational cut strictly below every displayed atom has cumulative mass
zero.  This is the finite certificate replacing a limit at negative
infinity. -/
theorem cumulative_eq_zero_of_cut_lt_all_atoms
    (distribution : Distribution Coordinate) (cut : Coordinate)
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
      simp only [atMostEvent, notAtMost, decide_false]
    _ = 0 := distribution.probability_false

/-- A rational cut at or above every displayed atom has cumulative mass one.
This is the finite certificate replacing a limit at positive infinity. -/
theorem cumulative_eq_one_of_all_atoms_le_cut
    (distribution : Distribution Coordinate) (cut : Coordinate)
    (above : ∀ atom, atom ∈ distribution.atoms → atom.item ≤ cut) :
    distribution.cumulative cut = 1 := by
  unfold cumulative
  calc
    distribution.probability (atMostEvent cut) =
        distribution.probability (fun _ => true) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      simp only [atMostEvent, above atom member, decide_true]
    _ = 1 := distribution.probability_true

/-- A certified rational gap in the displayed atom table makes the finite
cumulative law exactly flat across that gap. -/
theorem cumulative_eq_of_atom_gap
    (distribution : Distribution Coordinate)
    {lower upper : Coordinate} (order : lower ≤ upper)
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
    simp only [below, upperSelected, decide_true]
  · have lowerAbove : lower < atom.item := order.trans_lt above
    have notLower : ¬atom.item ≤ lower := lowerAbove.2
    have notUpper : ¬atom.item ≤ upper := above.2
    simp only [notLower, notUpper, decide_false]

/-- The cumulative probability of a finite rational mixture is the exact
weighted mixture of the two cumulative probabilities. -/
theorem cumulative_mixture
    (left right : Distribution Coordinate) (weight : MixingWeight)
    (threshold : Coordinate) :
    (left.mixture right weight).cumulative threshold =
      weight.coefficient * left.cumulative threshold +
        weight.complement * right.cumulative threshold :=
  left.mixture_probability right weight (atMostEvent threshold)

/-- Translating a finite rational distribution translates its cumulative
threshold by exact subtraction. -/
theorem cumulative_map_add (distribution : Distribution Coordinate)
    (shift threshold : Coordinate) :
    (distribution.map fun value => value + shift).cumulative threshold =
      distribution.cumulative (threshold - shift) := by
  unfold cumulative
  rw [distribution.map_probability]
  exact distribution.probability_congr _ _ (fun value => by
    change decide (value + shift ≤ threshold) =
      decide (value ≤ threshold - shift)
    by_cases shifted : value ≤ threshold - shift
    · have original : value + shift ≤ threshold :=
        (le_sub_iff_add_le.mp shifted)
      simp only [shifted, original, decide_true]
    · have original : ¬(value + shift ≤ threshold) := by
        intro order
        exact shifted (le_sub_iff_add_le.mpr order)
      simp only [shifted, original, decide_false])

/-- Multiplying a finite rational law by a positive rational factor divides
its cumulative threshold by that factor. -/
theorem cumulative_map_mul_pos
    (distribution : Distribution Coordinate)
    (factor threshold : Coordinate) (factorPositive : 0 < factor) :
    (distribution.map fun value => factor * value).cumulative threshold =
      distribution.cumulative (threshold / factor) := by
  unfold cumulative
  rw [distribution.map_probability]
  exact distribution.probability_congr _ _ (fun value => by
    change decide (factor * value ≤ threshold) =
      decide (value ≤ threshold / factor)
    by_cases divided : value ≤ threshold / factor
    · have original : factor * value ≤ threshold := by
        have scaled :=
          (RFAP.ConstructiveFraction.le_div_iff_pos factorPositive).1 divided
        simpa only [mul_comm] using scaled
      simp only [divided, original, decide_true]
    · have original : ¬factor * value ≤ threshold := by
        intro scaled
        apply divided
        apply (RFAP.ConstructiveFraction.le_div_iff_pos factorPositive).2
        simpa only [mul_comm] using scaled
      simp only [divided, original, decide_false])

/-- The finite cumulative function of a convolution is the exact average of
shifted cumulative functions of the right input. -/
theorem cumulative_convolve (left right : Distribution Coordinate)
    (threshold : Coordinate) :
    (left.convolve right).cumulative threshold =
      left.expectation (fun leftValue =>
        right.cumulative (threshold - leftValue)) := by
  unfold cumulative
  rw [left.convolve_probability]
  exact left.expectation_congr _ _ (fun leftValue =>
    right.probability_congr _ _ (fun rightValue => by
      change decide (leftValue + rightValue ≤ threshold) =
        decide (rightValue ≤ threshold - leftValue)
      by_cases shifted : rightValue ≤ threshold - leftValue
      · have original : leftValue + rightValue ≤ threshold := by
          have order := le_sub_iff_add_le.mp shifted
          simpa only [add_comm] using order
        simp only [shifted, original, decide_true]
      · have original : ¬(leftValue + rightValue ≤ threshold) := by
          intro order
          apply shifted
          apply le_sub_iff_add_le.mpr
          simpa only [add_comm] using order
        simp only [shifted, original, decide_false]))

private theorem atMost_union_interval
    {lower upper : Coordinate} (order : lower ≤ upper) (value : Coordinate) :
    unionEvent (atMostEvent lower)
        (openClosedIntervalEvent lower upper) value =
      atMostEvent upper value := by
  by_cases valueLeLower : value ≤ lower
  · have valueLeUpper := valueLeLower.trans order
    simp [unionEvent, atMostEvent, openClosedIntervalEvent,
      valueLeLower, valueLeUpper]
  · have lowerLtValue :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct valueLeLower
    by_cases valueLeUpper : value ≤ upper
    · simp [unionEvent, atMostEvent, openClosedIntervalEvent,
        valueLeLower, lowerLtValue, valueLeUpper]
    · simp [unionEvent, atMostEvent, openClosedIntervalEvent,
        valueLeLower, lowerLtValue, valueLeUpper]

private theorem atMost_disjoint_interval
    (distribution : Distribution Coordinate) (lower upper : Coordinate) :
    DisjointOn distribution.atoms (atMostEvent lower)
      (openClosedIntervalEvent lower upper) := by
  intro atom member selected
  have atomLeLower : atom.item ≤ lower := of_decide_eq_true selected.1
  have lowerLtAtom : lower < atom.item := by
    have intervalTrue := Bool.and_eq_true_iff.mp selected.2
    exact of_decide_eq_true intervalTrue.1
  exact (lowerLtAtom.2 atomLeLower).elim

/-- Exact mass of a rational half-open interval is the difference of the two
finite cumulative probabilities. -/
theorem probability_openClosedInterval
    (distribution : Distribution Coordinate)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    distribution.probability (openClosedIntervalEvent lower upper) =
      distribution.cumulative upper - distribution.cumulative lower := by
  have additive := distribution.probability_union_of_disjoint
    (atMost_disjoint_interval distribution lower upper)
  have unionEqual : distribution.probability
        (unionEvent (atMostEvent lower)
          (openClosedIntervalEvent lower upper)) =
      distribution.probability (atMostEvent upper) :=
    distribution.probability_congr _ _ (atMost_union_interval order)
  rw [unionEqual] at additive
  change distribution.probability (openClosedIntervalEvent lower upper) =
    distribution.probability (atMostEvent upper) -
      distribution.probability (atMostEvent lower)
  rw [additive]
  ring1

/-- Equivalently, a displayed atom gap has exactly zero probability mass in
its intervening rational half-open interval. -/
theorem probability_openClosedInterval_eq_zero_of_atom_gap
    (distribution : Distribution Coordinate)
    {lower upper : Coordinate} (order : lower ≤ upper)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ upper < atom.item) :
    distribution.probability (openClosedIntervalEvent lower upper) = 0 := by
  rw [distribution.probability_openClosedInterval order,
    ← distribution.cumulative_eq_of_atom_gap order gap]
  ring1

/-- If a displayed value is isolated from below by a rational cut, its exact
equality-event mass is the jump of the finite cumulative law across that
gap.  Repeated rows at the value are all counted. -/
theorem probability_eqValue_eq_cumulative_sub_of_atom_gap
    (distribution : Distribution Coordinate)
    {lower value : Coordinate} (lowerLtValue : lower < value)
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
        simp only [openClosedIntervalEvent, notEqual, notAboveLower,
          decide_false, Bool.false_and]
      · rcases equalOrAbove with equal | above
        · rw [equal]
          unfold openClosedIntervalEvent
          simp only [lowerLtValue, le_rfl, decide_true, Bool.true_and]
        · have notEqual : atom.item ≠ value := by
            intro equal
            rw [equal] at above
            exact (lt_irrefl _ above).elim
          have notAtMost : ¬atom.item ≤ value := above.2
          simp only [openClosedIntervalEvent, notEqual, notAtMost,
            decide_false, Bool.and_false]
    _ = distribution.cumulative value - distribution.cumulative lower :=
      distribution.probability_openClosedInterval lowerLtValue.le

end Distribution

end FiniteMeasure
