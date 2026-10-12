module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

@[expose] public section

namespace Purelib.Measure.Distribution

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- A sufficiently large upper-tail probability forces strictly-below-threshold probability below the supplied level. -/
theorem probability_strictlyBelow_lt_of_one_sub_lt_probability_atLeast
    {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) (level lower : Fraction.Rational)
    (tailLarge : 1 - level < distribution.probability
      (Measure.atLeastEvent lower value)) :
    distribution.probability (fun item => decide (value item < lower)) <
      level := by
  have tailComplement := distribution.probability_add_complement
    (fun item => decide (value item < lower))
  have complementProbability := distribution.probability_congr
    (Measure.complementEvent
      (fun item => decide (value item < lower)))
    (Measure.atLeastEvent lower value)
    (Event.complement_strictlyBelowProbe value lower)
  rw [complementProbability] at tailComplement
  exact Fraction.left_lt_of_add_eq_one_of_one_sub_lt_right
    (distribution.probability fun item => decide (value item < lower))
    (distribution.probability (Measure.atLeastEvent lower value))
    level tailComplement tailLarge

open Purelib in
open Purelib.Data.Rat in
/-- If probability strictly below a cut is less than the admissible level, that cut lies at or below the exact lower
quantile. -/
theorem lower_le_lowerQuantile_of_probability_strictlyBelow_lt
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower : Fraction.Rational)
    (belowLowerLt : distribution.probability
      (Measure.strictlyBelowEvent lower) < level) :
    lower ≤ distribution.lowerQuantile level levelPositive levelAtMostOne := by
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro quantileLtLower
  have cumulativeLeBelow :
      distribution.cumulative
          (distribution.lowerQuantile level levelPositive levelAtMostOne) ≤
        distribution.probability
          (Measure.strictlyBelowEvent lower) := by
    apply Measure.eventWeight_mono
    intro atom member selected
    have valueLeQuantile : atom.item ≤
        distribution.lowerQuantile level levelPositive levelAtMostOne :=
      of_decide_eq_true selected
    exact decide_eq_true
      (valueLeQuantile.trans_lt quantileLtLower)
  have levelLeBelow :=
    (distribution.level_le_cumulative_lowerQuantile level levelPositive
      levelAtMostOne).trans cumulativeLeBelow
  exact belowLowerLt.2 levelLeBelow
end Purelib.Measure.Distribution

end
