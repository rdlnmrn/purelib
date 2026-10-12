module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Rational quadratic bounds

Square comparisons and exact quadratic estimates retain the canonical rational
operations and the supplied sign and radius certificates. -/

public section

namespace Purelib.Data.Rat

/-- Every rational is at most its square plus one. -/
theorem Quadratic.coordinate_le_sq_add_one (value : Fraction.Rational) :
    value ≤ value ^ 2 + 1 := by
  by_cases nonpositive : value ≤ 0
  · exact nonpositive.trans
      (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct value)
        (show (0 : Fraction.Rational) ≤ 1 by decide))
  · have positive : 0 < value := lt_of_not_ge nonpositive
    by_cases atMostOne : value ≤ 1
    · have oneBound : (1 : Fraction.Rational) ≤ value ^ 2 + 1 := by
        have added := Fraction.Order.Arithmetic.add_le_add_right_direct
          (Fraction.Order.Arithmetic.sq_nonneg_direct value) 1
        calc
          1 = 0 + 1 := (Fraction.Field.zero_add 1).symm
          _ ≤ value ^ 2 + 1 := added
      exact atMostOne.trans oneBound
    · have oneLe : (1 : Fraction.Rational) ≤ value := (lt_of_not_ge atMostOne).le
      have squareBound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          oneLe positive.le
      have valueLeSquare : value ≤ value ^ 2 := by
        simpa only [Fraction.Field.mul_one_direct, pow_two] using
          squareBound
      have addOne : value ^ 2 ≤ value ^ 2 + 1 := by
        have added := Fraction.Order.Arithmetic.add_le_add_right_direct
          (show (0 : Fraction.Rational) ≤ 1 by decide) (value ^ 2)
        calc
          value ^ 2 = 0 + value ^ 2 :=
            (Fraction.Field.zero_add _).symm
          _ ≤ 1 + value ^ 2 := added
          _ = value ^ 2 + 1 := _root_.add_comm _ _
      exact valueLeSquare.trans addOne

/-- The negation of every rational is at most its square plus one. -/
theorem Quadratic.neg_coordinate_le_sq_add_one (value : Fraction.Rational) :
    -value ≤ value ^ 2 + 1 := by
  have same : (-value) ^ 2 = value ^ 2 := by ring1
  have bound := Quadratic.coordinate_le_sq_add_one (-value)
  rw [same] at bound
  exact bound

/-- A rational with square at most one is at most one. -/
theorem Quadratic.le_one_of_sq_le_one {value : Fraction.Rational}
    (square : value ^ 2 ≤ 1) : value ≤ 1 := by
  by_cases atMostOne : value ≤ 1
  · exact atMostOne
  · have oneLess : (1 : Fraction.Rational) < value := lt_of_not_ge atMostOne
    have positive : 0 < value := (show (0 : Fraction.Rational) < 1 by decide).trans
      oneLess
    have valueLessSquare : value < value ^ 2 := by
      have multiplied :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct oneLess
          positive
      simpa only [_root_.one_mul, pow_two] using
        multiplied
    have impossible : (1 : Fraction.Rational) < 1 :=
      oneLess.trans (valueLessSquare.trans_le square)
    exact (lt_irrefl 1 impossible).elim

/-- A rational with square at most one is at least negative one. -/
theorem Quadratic.neg_one_le_of_sq_le_one {value : Fraction.Rational}
    (square : value ^ 2 ≤ 1) : (-1 : Fraction.Rational) ≤ value := by
  have negated : -value ≤ (1 : Fraction.Rational) :=
    Quadratic.le_one_of_sq_le_one (value := -value) (by
      have same : (-value) ^ 2 = value ^ 2 := by ring1
      rw [same]
      exact square)
  simpa only [_root_.neg_neg] using
    Fraction.Order.Arithmetic.neg_le_neg_direct negated

/-- Half the square of a positive rational is strictly below its square.

The strict inequality retains the positive square and divides it by the fixed
positive rational denominator two. -/
theorem Quadratic.Bounds.half_sq_lt_sq {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) : epsilon ^ 2 / 2 < epsilon ^ 2 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  have squarePositive : 0 < epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  calc
    epsilon ^ 2 = epsilon ^ 2 * 1 := by ring1
    _ < epsilon ^ 2 * 2 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        squarePositive (by decide)

/-- The square of a rational sum is at most twice the sum of the squares. -/
theorem add_sq_le_two_mul_add_sq (left right : Fraction.Rational) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    2 * (left ^ 2 + right ^ 2) - (left + right) ^ 2 =
        (left - right) ^ 2 := by ring1
    _ ≥ 0 := Fraction.Order.Arithmetic.sq_nonneg_direct _

/-- Square the supplied rational radius to obtain its exact squared target. -/
@[expose] def Quadratic.Bounds.squaredRefinementTarget (radius : Fraction.Rational) : Fraction.Rational :=
  radius ^ 2

/-- A positive rational radius gives a positive squared target. -/
theorem Quadratic.Bounds.squaredRefinementTarget_positive {radius : Fraction.Rational}
    (positive : 0 < radius) : 0 < Quadratic.Bounds.squaredRefinementTarget radius := by
  unfold Quadratic.Bounds.squaredRefinementTarget
  exact Fraction.Order.Arithmetic.pow_pos_direct positive 2

/-- Every rational is at most its square plus one. -/
theorem Quadratic.Bounds.value_le_sq_add_one (value : Fraction.Rational) :
    value <= value ^ 2 + 1 := by
  by_cases positive : 0 < value
  · rcases le_total value 1 with small | large
    · exact small.trans (le_add_of_nonneg_left
        (Fraction.Order.Arithmetic.sq_nonneg_direct value))
    · calc
        value = value * 1 := by ring1
        _ <= value * value :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            large positive.le
        _ = value ^ 2 := by ring1
        _ <= value ^ 2 + 1 := le_add_of_nonneg_right (by decide)
  · have nonpositive : value <= 0 := le_of_not_gt positive
    exact nonpositive.trans
      (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct value)
        (by decide))

/-- The negation of every rational is at most its square plus one. -/
theorem Quadratic.Bounds.neg_value_le_sq_add_one (value : Fraction.Rational) :
    -value <= value ^ 2 + 1 := by
  calc
    -value <= (-value) ^ 2 + 1 := Quadratic.Bounds.value_le_sq_add_one (-value)
    _ = value ^ 2 + 1 := by ring1

/-- Multiplying a value inside strict symmetric radius bounds gives the stated negative quadratic-coefficient lower
bound. -/
theorem Quadratic.Bounds.weighted_lower_of_radius (coefficient delta radius : Fraction.Rational)
    (radiusPositive : 0 < radius) (lower : -radius < delta)
    (upper : delta < radius) :
    -((coefficient ^ 2 + 1) * radius) <= coefficient * delta := by
  rcases le_total 0 coefficient with nonnegative | nonpositive
  · have coefficientBound := Quadratic.Bounds.value_le_sq_add_one coefficient
    have scaledBound : coefficient * radius <=
        (coefficient ^ 2 + 1) * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientBound radiusPositive.le
    have negatedBound :=
      Fraction.Order.Arithmetic.neg_le_neg_direct scaledBound
    have scaledLower : coefficient * (-radius) <= coefficient * delta :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        lower.le nonnegative
    calc
      -((coefficient ^ 2 + 1) * radius) <= -(coefficient * radius) :=
        negatedBound
      _ = coefficient * (-radius) := by ring1
      _ <= coefficient * delta := scaledLower
  · let magnitude := -coefficient
    have magnitudeNonnegative : 0 <= magnitude := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonpositive
      simpa only [neg_zero, -eq_self, -iff_self] using reversed
    have magnitudeBound : magnitude <= coefficient ^ 2 + 1 := by
      simpa only [magnitude] using Quadratic.Bounds.neg_value_le_sq_add_one coefficient
    have scaledBound : magnitude * radius <=
        (coefficient ^ 2 + 1) * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        magnitudeBound radiusPositive.le
    have negatedBound :=
      Fraction.Order.Arithmetic.neg_le_neg_direct scaledBound
    have scaledUpper : magnitude * delta <= magnitude * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        upper.le magnitudeNonnegative
    have negatedUpper :=
      Fraction.Order.Arithmetic.neg_le_neg_direct scaledUpper
    calc
      -((coefficient ^ 2 + 1) * radius) <= -(magnitude * radius) :=
        negatedBound
      _ <= -(magnitude * delta) := negatedUpper
      _ = coefficient * delta := by
        dsimp only [magnitude]
        ring1

/-- Four times the product of two rationals is at most the square of their retained sum. -/
theorem Quadratic.Bounds.fixed_sum_product_bound (A B V : Fraction.Rational) (sum : A + B = V) :
    4 * A * B ≤ V ^ 2 := by
  have squareNonnegative : (0 : Fraction.Rational) ≤ (A - B) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct (A - B)
  have differenceNonnegative :
      (0 : Fraction.Rational) ≤ V ^ 2 - 4 * A * B := by
    calc
      0 ≤ (A - B) ^ 2 := squareNonnegative
      _ = V ^ 2 - 4 * A * B := by rw [← sum]; ring1
  exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    differenceNonnegative

end Purelib.Data.Rat
