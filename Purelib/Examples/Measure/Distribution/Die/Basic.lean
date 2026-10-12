module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Atomicity
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Cumulative.Support
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.LayerCake
import Purelib.Measure.Distribution.Median.Basic
import Purelib.Measure.Distribution.Median.L1
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Pushforward.Moments
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Quantile.TotalVariation
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Consolidation
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Content.Atomicity
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.EventAlgebra.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Die.Basic

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples

/-- The exact fair distribution on die faces one through six. -/
def fairDie : Distribution Nat where
  atoms :=
    [⟨1, 1 / 6, by decide⟩,
      ⟨2, 1 / 6, by decide⟩,
      ⟨3, 1 / 6, by decide⟩,
      ⟨4, 1 / 6, by decide⟩,
      ⟨5, 1 / 6, by decide⟩,
      ⟨6, 1 / 6, by decide⟩]
  total_one := by decide

/-- The fair die law pushed forward to canonical rational face values. -/
def rationalFairDie : Distribution Fraction.Rational :=
  fairDie.map fun face => (face : Fraction.Rational)

/-- The fair die coordinate has expectation seven halves. -/
theorem fairDie_coordinate_expectation :
    fairDie.expectation (fun face => (face : Fraction.Rational)) = 7 / 2 := by
  decide

/-- The fair die coordinate has second moment 91/6. -/
theorem fairDie_coordinate_secondMoment :
    fairDie.expectation (fun face => (face : Fraction.Rational) ^ 2) = 91 / 6 := by
  change
    (1 / 6 : Fraction.Rational) * 1 ^ 2 +
      ((1 / 6 : Fraction.Rational) * 2 ^ 2 +
      ((1 / 6 : Fraction.Rational) * 3 ^ 2 +
      ((1 / 6 : Fraction.Rational) * 4 ^ 2 +
      ((1 / 6 : Fraction.Rational) * 5 ^ 2 +
      ((1 / 6 : Fraction.Rational) * 6 ^ 2 + 0))))) = 91 / 6
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The fair die coordinate has variance 35/12. -/
theorem fairDie_coordinate_variance :
    fairDie.variance (fun face => (face : Fraction.Rational)) = 35 / 12 := by
  rw [fairDie.variance_eq_secondMoment_sub_sq,
    fairDie_coordinate_secondMoment,
      fairDie_coordinate_expectation]
  rw [pow_two, Fraction.Field.div_mul_div_direct,
    Fraction.Field.div_sub_div_direct]
  · apply Fraction.Field.div_eq_div_of_cross_mul
    · exact Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 6) (by decide)).ne'
        (Fraction.Field.mul_ne_zero_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 2) (by decide)).ne'
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 2) (by decide)).ne')
    · exact (Fraction.Cast.Order.natCast_pos_direct
        (n := 12) (by decide)).ne'
    · ring1
  · exact (Fraction.Cast.Order.natCast_pos_direct
      (n := 6) (by decide)).ne'
  · exact (Fraction.Cast.Order.natCast_pos_direct
      (n := 4) (by decide)).ne'

/-- The rational pushforward of the die law retains coordinate variance 35/12. -/
theorem rationalFairDie_coordinate_variance :
    rationalFairDie.variance (fun value => value) = 35 / 12 := by
  unfold rationalFairDie
  rw [Distribution.map_variance]
  exact fairDie_coordinate_variance

/-- The retained fair die distribution contains an atom with positive probability. -/
example : ∃ face : Nat, 0 < fairDie.probability (Purelib.Measure.atomEvent face) :=
  fairDie.exists_positive_singleton

/-- The finite fair die content is not atomless. -/
example : ¬fairDie.toContent.Atomless :=
  fairDie.not_atomless

/-- The fair die expectation equals its finite six-term natural tail-probability sum. -/
example : fairDie.expectation (fun face => (face : Fraction.Rational)) =
    fairDie.natTailProbabilitySum (fun face => face) 6 :=
  fairDie.expectation_nat_eq_natTailProbabilitySum_of_bounded
    (fun face => face) 6 (by decide)

/-- The finite fair die tail-probability sum is seven halves. -/
example : fairDie.natTailProbabilitySum (fun face => face) 6 = 7 / 2 := by
  decide

/-- The rational fair die cumulative probability at three is one half. -/
example : rationalFairDie.cumulative 3 = 1 / 2 := by
  decide

/-- The rational fair die cumulative probability at zero is zero. -/
example : rationalFairDie.cumulative 0 = 0 :=
  rationalFairDie.cumulative_eq_zero_of_cut_lt_all_atoms 0 (by decide)

/-- The rational fair die cumulative probability at seven is one. -/
example : rationalFairDie.cumulative 7 = 1 :=
  rationalFairDie.cumulative_eq_one_of_all_atoms_le_cut 7 (by decide)

/-- The rational fair die cumulative function is unchanged between three and seven halves. -/
example : rationalFairDie.cumulative 3 =
    rationalFairDie.cumulative (7 / 2) :=
  rationalFairDie.cumulative_eq_of_atom_gap (by decide) (by decide)

/-- The lower median of the rational fair die is three. -/
example : rationalFairDie.median = 3 := by
  decide

/-- The lower three-quarter quantile of the rational fair die is five. -/
example : rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) = 5 := by
  decide

/-- The atom-gap crossing certificate identifies the lower three-quarter quantile as five. -/
example : rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) = 5 :=
  rationalFairDie.lowerQuantile_eq_of_atom_gap_crossing
    (3 / 4) (by decide) (by decide) 4 5
      (by decide) (by decide) (by decide)

/-- The total-variation margin certificate brackets the three-quarter quantile above four and at most five. -/
example :
    4 < rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) ∧
      rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) ≤ 5 :=
  rationalFairDie.lowerQuantile_mem_bracket_of_totalVariation_margins
    rationalFairDie (3 / 4) (by decide) (by decide) 4 5
      (by decide) (by decide)

/-- The fair die probability strictly below its lower median is less than one half. -/
example : rationalFairDie.probability
      (Purelib.Measure.strictlyBelowEvent rationalFairDie.median) < 1 / 2 :=
  rationalFairDie.probability_strictlyBelow_median_lt_half

/-- The fair die probability at least its lower median is greater than one half. -/
example : 1 / 2 < rationalFairDie.probability
      (Purelib.Measure.atLeastCoordinateEvent rationalFairDie.median) :=
  rationalFairDie.half_lt_probability_atLeast_median

/-- The absolute deviation from the fair die median is three halves. -/
example : rationalFairDie.absoluteDeviation
  rationalFairDie.median = 3 / 2 := by
  decide

/-- The fair die median has no greater absolute deviation than the candidate seven. -/
example : rationalFairDie.absoluteDeviation
  rationalFairDie.median ≤
    rationalFairDie.absoluteDeviation 7 :=
  rationalFairDie.absoluteDeviation_median_le 7

/-- The absolute deviation from seven is seven halves. -/
example : rationalFairDie.absoluteDeviation 7 = 7 / 2 := by
  decide

/-- The retained half-quantile threshold does not exceed the retained three-quarter threshold. -/
example :
    (rationalFairDie.quantileCertificate
        (1 / 2) (by decide) (by decide)).threshold ≤
      (rationalFairDie.quantileCertificate
        (3 / 4) (by decide) (by decide)).threshold :=
  QuantileCertificate.threshold_mono
    (rationalFairDie.quantileCertificate (1 / 2) (by decide) (by decide))
    (rationalFairDie.quantileCertificate (3 / 4) (by decide) (by decide))
    (by decide)

/-- The rational fair die probability of (2,5] is one half. -/
example : rationalFairDie.probability
    (Purelib.Measure.openClosedIntervalEvent 2 5) = 1 / 2 := by
  decide

/-- The probability of (2,5] equals the cumulative difference at five and two. -/
example : rationalFairDie.probability
      (Purelib.Measure.openClosedIntervalEvent 2 5) =
    rationalFairDie.cumulative 5 -
      rationalFairDie.cumulative 2 :=
  rationalFairDie.probability_openClosedInterval (by decide)

/-- The probability of face five equals the cumulative difference across its preceding atom gap. -/
example : rationalFairDie.probability
      (fun value => decide (value = 5)) =
    rationalFairDie.cumulative 5 -
      rationalFairDie.cumulative 4 :=
  rationalFairDie.probability_eqValue_eq_cumulative_sub_of_atom_gap
    (by decide) (by decide)

/-- The retained cumulative-jump certificate at five has lower endpoint four. -/
example : (rationalFairDie.cumulativeJumpCertificate 5).lower = 4 := by
  decide

/-- The atom mass at five equals the cumulative jump certified by its retained predecessor bound. -/
example : rationalFairDie.atomMass 5 =
    rationalFairDie.cumulative 5 -
      rationalFairDie.cumulative
        (rationalFairDie.cumulativeJumpCertificate 5).lower :=
  rationalFairDie.atomMass_eq_cumulative_sub_jumpCertificate 5

end Purelib.Examples.Measure.Distribution.Die.Basic

end
