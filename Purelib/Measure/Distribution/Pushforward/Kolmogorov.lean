module
import Purelib.Measure.Distribution.Pushforward.Cumulative
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

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

open Purelib.Data.Rat
/-- Translating both original laws by the same shift preserves Kolmogorov distance. -/
theorem kolmogorovDistance_map_add_eq
    (left right : Distribution Fraction.Rational) (shift : Fraction.Rational) :
    (left.map fun value => value + shift).kolmogorovDistance
        (right.map fun value => value + shift) =
      left.kolmogorovDistance right := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (left.map fun value => value + shift).kolmogorovDistance_le
      (right.map fun value => value + shift)
      (left.kolmogorovDistance right)
      (left.kolmogorovDistance_nonnegative right)
    intro cut
    rw [left.cumulative_map_add shift cut,
      right.cumulative_map_add shift cut]
    exact left.cumulative_separation_leKolmogorovDistance right
      (cut - shift)
  · apply left.kolmogorovDistance_le right
      ((left.map fun value => value + shift).kolmogorovDistance
        (right.map fun value => value + shift))
      ((left.map fun value => value + shift)
        |>.kolmogorovDistance_nonnegative
          (right.map fun value => value + shift))
    intro cut
    have shiftedBound :=
      (left.map fun value => value + shift)
        |>.cumulative_separation_leKolmogorovDistance
          (right.map fun value => value + shift) (cut + shift)
    rw [left.cumulative_map_add shift (cut + shift),
      right.cumulative_map_add shift (cut + shift)] at shiftedBound
    simpa only [add_sub_cancel_right] using shiftedBound

/-- Scaling both original laws by the same positive factor preserves Kolmogorov distance. -/
theorem kolmogorovDistance_map_mul_pos_eq
    (left right : Distribution Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor) :
    (left.map fun value => factor * value).kolmogorovDistance
        (right.map fun value => factor * value) =
      left.kolmogorovDistance right := by
  have factorNonzero : factor ≠ 0 := factorPositive.ne'
  have cancel : ∀ cut : Fraction.Rational, (cut * factor) / factor = cut := by
    intro cut
    calc
      (cut * factor) / factor =
          (factor * cut) / (factor * 1) := by
        apply congrArg₂ (fun numerator denominator : Fraction.Rational =>
          numerator / denominator)
        · exact Fraction.Field.mul_comm cut factor
        · exact (Fraction.Field.mul_one_direct factor).symm
      _ = cut / 1 :=
        Fraction.Field.mul_div_mul_left_direct
          factor cut 1 factorNonzero
      _ = cut := by
        have cancelled :=
          Fraction.Field.div_mul_cancel_of_ne cut 1 (by decide)
        rw [Fraction.Field.mul_one_direct] at cancelled
        exact cancelled
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (left.map fun value => factor * value).kolmogorovDistance_le
      (right.map fun value => factor * value)
      (left.kolmogorovDistance right)
      (left.kolmogorovDistance_nonnegative right)
    intro cut
    rw [left.cumulative_map_mul_pos factor cut factorPositive,
      right.cumulative_map_mul_pos factor cut factorPositive]
    exact left.cumulative_separation_leKolmogorovDistance right
      (cut / factor)
  · apply left.kolmogorovDistance_le right
      ((left.map fun value => factor * value).kolmogorovDistance
        (right.map fun value => factor * value))
      ((left.map fun value => factor * value)
        |>.kolmogorovDistance_nonnegative
          (right.map fun value => factor * value))
    intro cut
    have scaledBound :=
      (left.map fun value => factor * value)
        |>.cumulative_separation_leKolmogorovDistance
          (right.map fun value => factor * value) (cut * factor)
    rw [left.cumulative_map_mul_pos factor (cut * factor) factorPositive,
      right.cumulative_map_mul_pos factor (cut * factor) factorPositive,
      cancel cut] at scaledBound
    exact scaledBound
end Distribution

end Purelib.Measure

end
