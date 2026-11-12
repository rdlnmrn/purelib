module
import Purelib.Approximation.Rational.Segment.Increment
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! A finite quadratic increment estimate on the rational unit segment. -/

namespace TestPurelib.Approximation.Rational.Segment.Increment

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- A rational square on the original unit interval. -/
private def square (point : Fraction.Rational) : Fraction.Rational := point ^ 2

/-- Its finite local lower bound retains a nonzero quadratic remainder. -/
private theorem localBound {first last : Fraction.Rational}
    (_firstInside : (⟨0, 1, by decide⟩ : Purelib.Data.Rat.Interval).Contains first)
    (lastInside : (⟨0, 1, by decide⟩ : Purelib.Data.Rat.Interval).Contains last) (ordered : last ≤ first) :
    0 * (first - last) - 1 * (first - last) ^ 2 ≤ square first - square last := by
  have distance := Arithmetic.sub_nonneg_direct ordered
  have product := Arithmetic.mul_nonneg_direct lastInside.1 distance
  have squared := Arithmetic.sq_nonneg_direct (first - last)
  have twice := Arithmetic.add_le_add_direct product product
  have squares := Arithmetic.add_le_add_direct squared squared
  have all := Arithmetic.add_le_add_direct twice squares
  have identity : 0 * (first - last) - 1 * (first - last) ^ 2 +
      (last * (first - last) + last * (first - last) +
        ((first - last) ^ 2 + (first - last) ^ 2)) = square first - square last := by
    unfold square
    ring1
  have zero : (0 : Fraction.Rational) + 0 + (0 + 0) = 0 := by decide
  rw [zero] at all
  have shifted := Arithmetic.add_le_add_right_direct all
    (0 * (first - last) - 1 * (first - last) ^ 2)
  have commute : (last * (first - last) + last * (first - last) +
      ((first - last) ^ 2 + (first - last) ^ 2)) +
      (0 * (first - last) - 1 * (first - last) ^ 2) = square first - square last := by
    rw [← identity]
    ring1
  rw [Fraction.Field.zero_add, commute] at shifted
  exact shifted

example {first last : Fraction.Rational}
    (firstInside : (⟨0, 1, by decide⟩ : Purelib.Data.Rat.Interval).Contains first)
    (lastInside : (⟨0, 1, by decide⟩ : Purelib.Data.Rat.Interval).Contains last) (ordered : last ≤ first) :
    0 * (first - last) ≤ square first - square last :=
  Segment.Increment.remove_quadratic square ⟨0, 1, by decide⟩ 0 1 (by decide) localBound
    firstInside lastInside ordered

end TestPurelib.Approximation.Rational.Segment.Increment
