module
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

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

open Purelib.Data.Rat
/-- Translating all payloads translates cumulative thresholds by the opposite shift. -/
theorem cumulative_map_add (distribution : Distribution Fraction.Rational)
    (shift threshold : Fraction.Rational) :
    (distribution.map fun value => value + shift).cumulative threshold =
      distribution.cumulative (threshold - shift) := by
  unfold cumulative
  rw [distribution.map_probability]
  exact distribution.probability_congr _ _ (fun value => by
    change decide (value + shift ≤ threshold) =
      decide (value ≤ threshold - shift)
    by_cases shifted : value ≤ threshold - shift
    · have original : value + shift ≤ threshold :=
        by
          have translated := Fraction.Order.Arithmetic.add_le_add_right_direct shifted shift
          have restore : (threshold - shift) + shift = threshold := by ring1
          exact restore ▸ translated
      simp only [-eq_self, -iff_self, decide_eq_true shifted, decide_eq_true original]
      rfl
    · have original : ¬(value + shift ≤ threshold) := by
        intro order
        apply shifted
        have translated := Fraction.Order.Arithmetic.add_le_add_right_direct order (-shift)
        have restoreLeft : (value + shift) + -shift = value := by ring1
        have restoreRight : threshold + -shift = threshold - shift := by ring1
        exact restoreLeft ▸ restoreRight ▸ translated
      simp only [-eq_self, -iff_self, decide_eq_false shifted, decide_eq_false original]
      rfl)

/-- Multiplying all payloads by a positive factor divides cumulative thresholds by that factor. -/
theorem cumulative_map_mul_pos
    (distribution : Distribution Fraction.Rational)
    (factor threshold : Fraction.Rational) (factorPositive : 0 < factor) :
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
          (Fraction.Order.Field.le_div_iff_pos factorPositive).1 divided
        simpa only [-eq_self, -iff_self, mul_comm] using scaled
      simp only [-eq_self, -iff_self, decide_eq_true divided, decide_eq_true original]
      rfl
    · have original : ¬factor * value ≤ threshold := by
        intro scaled
        apply divided
        apply (Fraction.Order.Field.le_div_iff_pos factorPositive).2
        simpa only [-eq_self, -iff_self, mul_comm] using scaled
      simp only [-eq_self, -iff_self, decide_eq_false divided, decide_eq_false original]
      rfl)
end Distribution

end Purelib.Measure

end

section
section
public section

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- Occurrencewise separation bounds compare two pushforward cumulative probabilities after increasing the right
threshold by the retained radius. -/
theorem map_cumulative_le_add_of_rationalSeparation_le {α : Type}
    (source : Distribution α) (left right : α → Fraction.Rational)
    (radius cut : Fraction.Rational)
    (close : ∀ atom, atom ∈ source.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    (source.map left).cumulative cut ≤
      (source.map right).cumulative (cut + radius) := by
  unfold cumulative
  rw [source.map_probability, source.map_probability]
  apply eventWeight_mono
  intro atom member selected
  have leftLeCut : left atom.item ≤ cut := of_decide_eq_true selected
  have rightMinusLeft : right atom.item - left atom.item ≤ radius :=
    (Fraction.Order.Basic.le_max_right (left atom.item - right atom.item)
      (right atom.item - left atom.item)).trans (close atom member)
  have rightLeRadiusAddLeft :
      right atom.item ≤ radius + left atom.item :=
    Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp rightMinusLeft
  apply decide_eq_true
  calc
    right atom.item ≤ radius + left atom.item := rightLeRadiusAddLeft
    _ ≤ radius + cut :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl leftLeCut
    _ = cut + radius := by ring1
namespace EvaluationEquivalent
end EvaluationEquivalent
end Distribution

end Purelib.Measure

end

end
