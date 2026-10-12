module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Convolution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

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

open Purelib.Data.Rat in
/-- A convolution's cumulative probability is the original left expectation of right cumulative probabilities at
translated thresholds. -/
theorem cumulative_convolve (left right : Distribution Fraction.Rational)
    (threshold : Fraction.Rational) :
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
          have translated := Fraction.Order.Arithmetic.add_le_add_right_direct shifted leftValue
          have restore : (threshold - leftValue) + leftValue = threshold := by ring1
          exact (Fraction.add_comm rightValue leftValue) ▸ (restore ▸ translated)
        simp only [-eq_self, -iff_self, decide_eq_true shifted, decide_eq_true original]
        rfl
      · have original : ¬(leftValue + rightValue ≤ threshold) := by
          intro order
          apply shifted
          have translated := Fraction.Order.Arithmetic.add_le_add_right_direct order (-leftValue)
          have restoreLeft : (leftValue + rightValue) + -leftValue = rightValue := by ring1
          have restoreRight : threshold + -leftValue = threshold - leftValue := by ring1
          exact restoreLeft ▸ restoreRight ▸ translated
        simp only [-eq_self, -iff_self, decide_eq_false shifted, decide_eq_false original]
        rfl))
end Distribution

end Purelib.Measure

end
