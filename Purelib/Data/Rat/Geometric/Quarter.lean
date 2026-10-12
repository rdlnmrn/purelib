module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Subtraction

/-!
# Quarter powers and finite rational geometric allowances

The original rational powers, finite sums and scaled allowances retain their
exact arithmetic data. Their certificates concern supplied finite indices
and nonnegative or positive scales, without an infinite completion.
-/

namespace Purelib.Data.Rat.Geometric.Quarter

open Purelib
open Purelib.Algebra
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Geometric
open Purelib.Data.Nat

/-- Each successor power of one quarter is at most its predecessor power.

The successor multiplies the original preceding quarter power by one
quarter. That nonnegative factor is at most one, giving the displayed
bound on the same retained predecessor power. -/
public theorem quarter_pow_succ_le (degree : Nat) :
    (1 / 4 : Fraction.Rational) ^ (degree + 1) ≤ (1 / 4 : Fraction.Rational) ^ degree := by
  rw [pow_succ]
  calc
    (1 / 4 : Fraction.Rational) ^ degree * (1 / 4) ≤
        (1 / 4 : Fraction.Rational) ^ degree * 1 :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (show (1 / 4 : Fraction.Rational) ≤ 1 by decide)
        (show 0 ≤ (1 / 4 : Fraction.Rational) ^ degree from
          Order.Arithmetic.pow_nonneg_direct (by decide) degree)
    _ = (1 / 4 : Fraction.Rational) ^ degree :=
      Fraction.Field.mul_one_direct _

/-- Advancing a quarter-power index is equivalent to dividing its rational scale by four.

The successor quarter power contributes one factor of one quarter.
Associativity and commutativity move that factor to the supplied scale,
which gives the same rational value as dividing the scale by four. -/
public theorem geometric_scale_shift (scale : Fraction.Rational) (index : Nat) :
    scale * (1 / 4 : Fraction.Rational) ^ (index + 1) =
      (scale / 4) * (1 / 4 : Fraction.Rational) ^ index := by
  rw [pow_succ]
  have scaleQuarter :
      scale * (1 / 4 : Fraction.Rational) = scale / 4 := by
    rw [Field.ExplicitField.div_eq_mul_inv,
      Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  calc
    scale * ((1 / 4 : Fraction.Rational) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Fraction.Rational)) * (1 / 4 : Fraction.Rational) ^ index := by
      ring1
    _ = (scale / 4) * (1 / 4 : Fraction.Rational) ^ index := by
      rw [scaleQuarter]

/-- Compute the finite sum of the first natural-number count of powers of one quarter.

The original recursion starts at zero and appends the next exact quarter
power at each successor. Its finite sum retains the supplied natural count. -/
@[expose] public def quarterSum : Nat → Fraction.Rational
  | 0 => 0
  | count + 1 => Purelib.Data.Rat.Geometric.Quarter.quarterSum count + (1 / 4 : Fraction.Rational) ^ count

/-- The finite quarter-power sum plus its exact geometric remainder is four thirds.

The original finite sum retains the displayed number of consecutive
quarter powers. Its remaining quarter power carries the exact rational
factor four thirds in this finite arithmetic identity. -/
public theorem quarterSum_remainder : ∀ count,
    quarterSum count + (4 / 3 : Fraction.Rational) * (1 / 4) ^ count = 4 / 3
  | 0 => by rw [quarterSum, pow_zero]; decide
  | count + 1 => by
      rw [quarterSum, pow_succ]
      calc
        quarterSum count + (1 / 4 : Fraction.Rational) ^ count +
            (4 / 3 : Fraction.Rational) *
              ((1 / 4 : Fraction.Rational) ^ count * (1 / 4)) =
            quarterSum count +
              (1 + (4 / 3 : Fraction.Rational) * (1 / 4)) *
                (1 / 4 : Fraction.Rational) ^ count := by ring1
        _ = quarterSum count +
              (4 / 3 : Fraction.Rational) * (1 / 4) ^ count := by
            rw [show (1 : Fraction.Rational) + (4 / 3) * (1 / 4) = 4 / 3 by decide]
        _ = 4 / 3 := Purelib.Data.Rat.Geometric.Quarter.quarterSum_remainder count

/-- Every finite sum of successive quarter powers is at most four thirds.

The retained exact remainder is nonnegative at each finite count.
Removing that same rational remainder bounds the original finite sum. -/
public theorem quarterSum_le (count : Nat) : quarterSum count ≤ 4 / 3 := by
  have remainderNonnegative :
      0 ≤ (4 / 3 : Fraction.Rational) * (1 / 4) ^ count :=
    Order.Arithmetic.mul_nonneg_direct (by decide)
      (Order.Arithmetic.pow_nonneg_direct (by decide) count)
  calc
    quarterSum count ≤
        quarterSum count + (4 / 3 : Fraction.Rational) * (1 / 4) ^ count :=
      le_add_of_nonneg_right remainderNonnegative
    _ = 4 / 3 := quarterSum_remainder count

/-- Twice an odd-index half power equals the corresponding quarter power.

The original odd-index half power retains index two times the supplied
count plus one. Its displayed factor two gives exactly the quarter power
at the original count. -/
public theorem twice_half_odd_power : ∀ index,
    (2 : Fraction.Rational) * (1 / 2 : Fraction.Rational) ^ (2 * index + 1) =
      (1 / 4 : Fraction.Rational) ^ index
  | 0 => by decide
  | index + 1 => by
      rw [show 2 * (index + 1) + 1 = (2 * index + 1) + 2 by ring1,
        pow_add]
      calc
        (2 : Fraction.Rational) *
            ((1 / 2 : Fraction.Rational) ^ (2 * index + 1) * (1 / 2) ^ 2) =
            (2 * (1 / 2 : Fraction.Rational) ^ (2 * index + 1)) *
              (1 / 2) ^ 2 := by ring1
        _ = (1 / 4 : Fraction.Rational) ^ index * (1 / 2) ^ 2 := by
          rw [Purelib.Data.Rat.Geometric.Quarter.twice_half_odd_power index]
        _ = (1 / 4 : Fraction.Rational) ^ index * (1 / 4) := by
          rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]
        _ = (1 / 4 : Fraction.Rational) ^ (index + 1) := (pow_succ _ _).symm

/-- Increasing a natural exponent decreases the corresponding power of one quarter.

The retained order determines the explicit natural difference between
indices. The extra quarter power is between zero and one, so multiplying
the original earlier power by it can only decrease that power. -/
public theorem quarterPower_antitone {earlier later : Nat} (order : earlier ≤ later) :
    (1 / 4 : Fraction.Rational) ^ later ≤ (1 / 4 : Fraction.Rational) ^ earlier := by
  let extra := later - earlier
  have extension : earlier + extra = later := Subtraction.add_sub_of_le order
  rw [← extension]
  rw [pow_add]
  have extraLe : (1 / 4 : Fraction.Rational) ^ extra ≤ 1 := by
    have powerOrder := Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1 / 4)
      (by decide : (1 / 4 : Fraction.Rational) ≤ 1) extra
    simpa only [one_pow] using powerOrder
  calc
    (1 / 4 : Fraction.Rational) ^ earlier * (1 / 4 : Fraction.Rational) ^ extra ≤
        (1 / 4 : Fraction.Rational) ^ earlier * 1 :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct extraLe
        (Order.Arithmetic.pow_nonneg_direct (by decide) earlier)
    _ = (1 / 4 : Fraction.Rational) ^ earlier := by ring1

end Purelib.Data.Rat.Geometric.Quarter
