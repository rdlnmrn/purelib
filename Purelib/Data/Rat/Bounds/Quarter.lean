module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Nat.Order
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! Exact rational quarter, half and eighth scaling laws. -/

namespace Purelib.Data.Rat.Bounds.Quarter

open Purelib.Data.Rat
open Purelib.Algebra
open scoped Purelib.Data.Nat

/-- One quarter of a positive rational is positive. -/
public theorem quarter_pos {target : Fraction.Rational} (positive : 0 < target) :
    0 < target / 4 :=
  Fraction.Order.Field.div_pos_direct positive (by decide)

/-- Twice the sum of two quarters of a rational is the original rational.

Cancellation by the nonzero rational denominators identifies the two-quarter
sum with one half. Multiplying that half by two recovers the same input. -/
private theorem four_quarters (target : Fraction.Rational) :
    2 * (target / 4 + target / 4) = target := by
  have quarterSum : target / 4 + target / 4 = target / 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (4 : Fraction.Rational) ≠ 0 by decide)
    calc
      (target / 4 + target / 4) * 4 =
          (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
      _ = target + target := by
        rw [show target / 4 * 4 = target from
          Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 2) * 2) * 2 := by
        rw [show target / 2 * 2 = target from
          Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
      _ = (target / 2) * (2 * 2) :=
        Fraction.Field.mul_assoc (target / 2) 2 2
      _ = (target / 2) * 4 := by
        rw [show (2 : Fraction.Rational) * 2 = 4 by decide]
  rw [quarterSum, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)

/-- One sixteenth of the square of a positive rational is positive. -/
public theorem target_positive {delta : Fraction.Rational} (positive : 0 < delta) : 0 < delta ^ 2 / 16 :=
  Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.pow_pos_direct positive 2) (by decide)

/-- The square of one quarter of a rational is one sixteenth of its square. -/
public theorem quarter_square (delta : Fraction.Rational) : (delta / 4) ^ 2 = delta ^ 2 / 16 := by
  rw [pow_two, Fraction.Field.div_mul_div_direct, ← pow_two, show (4 : Fraction.Rational) * 4 = 16 by decide]

/-- Half of a rational is twice its quarter.

Multiplication by the nonzero denominator two reduces the statement to
the exact quarter denominator identity, with no sign restriction on the input. -/
public theorem half_eq_two_quarters (delta : Fraction.Rational) : delta / 2 = (delta / 4) * 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := (2 : Fraction.Rational)) (by decide)
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (2 : Fraction.Rational) ≠ 0)]
  calc
    delta = (delta / 4) * 4 := (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)).symm
    _ = ((delta / 4) * 2) * 2 := by ring1

/-- Multiplying half of a rational by two recovers that rational. -/
public theorem half_mul_two (value : Fraction.Rational) :
    (value / 2) * 2 = value :=
  Fraction.Field.div_mul_cancel_of_ne value 2 (by decide)

/-- Multiplying one eighth of a rational by eight recovers that rational. -/
private theorem eighth_mul_eight (value : Fraction.Rational) :
    (value / 8) * 8 = value :=
  Fraction.Field.div_mul_cancel_of_ne value 8 (by decide)

/-- Eight times one thirty-second of a rational equals one quarter of it.

The nonzero denominators four and thirty-two permit scalar cancellation.
Their exact factor of eight preserves the original rational input. -/
public theorem eight_div_thirtyTwo (target : Fraction.Rational) :
    8 * (target / 32) = target / 4 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 32) (by decide)).ne'
  calc
    (8 * (target / 32)) * 32 = 8 * ((target / 32) * 32) :=
      Fraction.Field.mul_assoc 8 (target / 32) 32
    _ = 8 * target := by
      rw [show (target / 32) * 32 = target from
        Fraction.Field.div_mul_cancel_of_ne target 32
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 32) (by decide)).ne']
    _ = target * 8 := Fraction.Field.mul_comm 8 target
    _ = ((target / 4) * 4) * 8 := by
      rw [show (target / 4) * 4 = target from
        Fraction.Field.div_mul_cancel_of_ne target 4
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by decide)).ne']
    _ = (target / 4) * (4 * 8) :=
      Fraction.Field.mul_assoc (target / 4) 4 8
    _ = (target / 4) * 32 := by
      rw [show (4 : Fraction.Rational) * 8 = 32 by ring1]

/-- The sum of half and one quarter of a positive rational is strictly smaller than the original rational.

The positive remaining quarter gives a direct strict translation bound.
Exact half and quarter denominator equations identify the complete sum. -/
public theorem half_add_quarter_lt {target : Fraction.Rational}
    (positive : 0 < target) : target / 2 + target / 4 < target := by
  have quarterPositive : 0 < target / 4 :=
    Fraction.Order.Field.div_pos_direct positive (by decide)
  have quarters : target / 4 + target / 4 = target / 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (4 : Fraction.Rational) ≠ 0 by decide)
    calc
      (target / 4 + target / 4) * 4 =
          (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
      _ = target + target := by
        rw [show (target / 4) * 4 = target from
          Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 2) * 2) * 2 := by
        rw [show (target / 2) * 2 = target from
          Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
      _ = (target / 2) * 4 := by ring1
  have halves : target / 2 + target / 2 = target := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (2 : Fraction.Rational) ≠ 0 by decide)
    calc
      (target / 2 + target / 2) * 2 =
          (target / 2) * 2 + (target / 2) * 2 := by rw [add_mul]
      _ = target + target := by
        rw [show (target / 2) * 2 = target from
          Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
      _ = target * 2 := by ring1
  have addQuarter := Fraction.Order.Arithmetic.add_lt_add_left_direct
    quarterPositive (target / 2 + target / 4)
  calc
    target / 2 + target / 4 = target / 2 + target / 4 + 0 := by ring1
    _ < target / 2 + target / 4 + target / 4 := addQuarter
    _ = target / 2 + (target / 4 + target / 4) := by ring1
    _ = target / 2 + target / 2 := by rw [quarters]
    _ = target := halves

/-- Four times the sum of two eighths of a rational recovers the original rational. -/
public theorem eight_eighths (target : Fraction.Rational) :
    4 * (target / 8 + target / 8) = target := by
  have half : target / 8 + target / 8 = target / 4 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (8 : Fraction.Rational) ≠ 0 by decide)
    calc
      (target / 8 + target / 8) * 8 =
          (target / 8) * 8 + (target / 8) * 8 := by rw [add_mul]
      _ = target + target := by
        rw [show target / 8 * 8 = target from
          Fraction.Field.div_mul_cancel_of_ne target 8 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 4) * 4) * 2 := by
        rw [show target / 4 * 4 = target from
          Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
      _ = (target / 4) * 8 := by ring1
  rw [half, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)

/-- One eighth of a positive rational is positive. -/
public theorem eighth_pos {target : Fraction.Rational} (positive : 0 < target) :
    0 < target / 8 :=
  Fraction.Order.Field.div_pos_direct positive (by decide)

/-- The sum of two quarters of a rational equals half of that rational. -/
public theorem two_quarters (target : Fraction.Rational) :
    target / 4 + target / 4 = target / 2 := by
  have twoAsQuotient : (2 / 1 : Fraction.Rational) = 2 := by
    calc
      (2 / 1 : Fraction.Rational) = (2 / 1) * 1 :=
        (Fraction.Field.mul_one_direct _).symm
      _ = 2 :=
        Fraction.Field.div_mul_cancel_of_ne 2 1 (by decide)
  calc
    target / 4 + target / 4 = (target / 4) * 2 := by ring1
    _ = (target / 4) * (2 / 1) := by rw [twoAsQuotient]
    _ = (target * 2) / (4 * 1) :=
      Fraction.Field.div_mul_div_direct target 4 2 1
    _ = (2 * target) / (2 * 2) := by
      rw [Fraction.Field.mul_comm target 2]
      apply congrArg (fun denominator : Fraction.Rational =>
        (2 * target) / denominator)
      decide
    _ = target / 2 :=
      Fraction.Field.mul_div_mul_left_direct 2 target 2
        (by decide)

end Purelib.Data.Rat.Bounds.Quarter

public section

namespace Purelib.Data.Rat.Bounds.Quarter

open Purelib.Data.Rat
/-- A quarter of a positive rational is strictly smaller than that rational.

Multiplication by the positive quarter transports the literal strict bound
from one to four, and cancellation by four recovers the original target. -/
public theorem quarter_lt_self {target : Fraction.Rational} (positive : 0 < target) : target / 4 < target := by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct quarterPositive (by
      decide : (1 : Fraction.Rational) < 4)
  rw [Fraction.Field.mul_one_direct] at ordered
  exact ordered.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end Purelib.Data.Rat.Bounds.Quarter

end
