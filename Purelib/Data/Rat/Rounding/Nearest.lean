module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Rounding.Floor

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Constructive nearest-Gaussian-integer arithmetic

This is the finite arithmetic kernel for a Hurwitz continued fraction over
the Gaussian integers.  Ties are resolved coordinatewise toward the positive
integer: `nearestCoordinate x = floor (x + 1/2)`.  Consequently the displayed
remainder lies in the half-open square `[-1/2, 1/2)²` and has quadrance at
most `1/2`.
-/

open Purelib.Data.Rat
open Purelib.Data.Int
open Purelib.Algebra.Ring

namespace Purelib.Data.Rat.Rounding.Nearest

/-- Round a rational to the nearest integer, choosing the larger integer at half-integer ties.

Compute the Euclidean floor after adding one half. The resulting displacement lies between negative one half inclusively
and positive one half exclusively, which specifies the tie direction. -/
@[expose] def nearestCoordinate (value : Fraction.Rational) : Int :=
  Rounding.Floor.floor (value + 1 / 2)

/-- The displacement from the chosen nearest integer lies in the half-open interval from negative one half to one half.

The same computed floor bounds the shifted rational on both sides, retaining the half-open tie convention. -/
theorem nearestCoordinate_error_bounds (value : Fraction.Rational) :
    -(1 / 2 : Fraction.Rational) ≤
        value - (nearestCoordinate value : Fraction.Rational) ∧
      value - (nearestCoordinate value : Fraction.Rational) < 1 / 2 := by
  let shifted := value + (1 / 2 : Fraction.Rational)
  let selected := Rounding.Floor.floor shifted
  have selectedLower : (selected : Fraction.Rational) ≤ shifted := by
    exact Rounding.Floor.intCast_floor_le shifted
  have selectedUpper :
      shifted < ((selected + 1 : Int) : Fraction.Rational) := by
    exact Rounding.Floor.lt_intCast_floor_add_one shifted
  have lowerBase : (selected : Fraction.Rational) - 1 / 2 ≤ value := by
    calc
      (selected : Fraction.Rational) - 1 / 2 ≤ shifted - 1 / 2 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct selectedLower
          (-(1 / 2 : Fraction.Rational))
      _ = value := by
        dsimp only [shifted]
        ring1
  have lowerShifted :=
    Fraction.Order.Arithmetic.add_le_add_right_direct lowerBase
      (-(selected : Fraction.Rational))
  have upperBase : value < (selected : Fraction.Rational) + 1 / 2 := by
    have translated :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct selectedUpper
        (-(1 / 2 : Fraction.Rational))
    calc
      value = shifted - 1 / 2 := by
        dsimp only [shifted]
        ring1
      _ < (((selected + 1 : Int) : Fraction.Rational) - 1 / 2) := translated
      _ = (selected : Fraction.Rational) + 1 / 2 := by
        rw [IntCast.add, Int.cast_one]
        calc
          (selected : Fraction.Rational) + 1 - 1 / 2 =
              (selected : Fraction.Rational) + (1 - 1 / 2) := by ring1
          _ = (selected : Fraction.Rational) + 1 / 2 := by
            rw [show (1 : Fraction.Rational) - 1 / 2 = 1 / 2 by decide]
  have upperShifted :=
    Fraction.Order.Arithmetic.add_lt_add_right_direct upperBase
      (-(selected : Fraction.Rational))
  change
    -(1 / 2 : Fraction.Rational) ≤
        value - (Rounding.Floor.floor
          (value + 1 / 2) : Fraction.Rational) ∧
      value - (Rounding.Floor.floor
        (value + 1 / 2) : Fraction.Rational) < 1 / 2
  constructor
  · change
      -(1 / 2 : Fraction.Rational) ≤ value - (selected : Fraction.Rational)
    calc
      -(1 / 2 : Fraction.Rational) =
          ((selected : Fraction.Rational) - 1 / 2) - selected := by ring1
      _ ≤ value - selected := lowerShifted
  · change value - (selected : Fraction.Rational) < (1 / 2 : Fraction.Rational)
    calc
      value - (selected : Fraction.Rational) <
          ((selected : Fraction.Rational) + 1 / 2) - selected := upperShifted
      _ = 1 / 2 := by ring1

/-- The chosen nearest integer minimizes squared displacement among all integers.

The half-interval displacement bounds compare the chosen integer with any competitor through their integer difference.
This retains an exact rational squared-distance inequality without introducing a real completion. -/
theorem nearestCoordinate_sq_le (value : Fraction.Rational) (competitor : Int) :
    (value - (nearestCoordinate value : Fraction.Rational)) ^ 2 ≤
      (value - (competitor : Fraction.Rational)) ^ 2 := by
  let selected := nearestCoordinate value
  let error : Fraction.Rational := value - (selected : Fraction.Rational)
  let gapInt : Int := competitor - selected
  let gap : Fraction.Rational := (gapInt : Fraction.Rational)
  have bounds := nearestCoordinate_error_bounds value
  have errorLower : -(1 / 2 : Fraction.Rational) ≤ error := by
    exact bounds.1
  have errorUpper : error < 1 / 2 := by
    exact bounds.2
  by_cases gapZero : gapInt = 0
  · have competitorSelected : competitor = selected := by
      dsimp only [gapInt] at gapZero
      apply Arithmetic.add_right_cancel (offset := -selected)
      calc
        competitor + -selected = 0 := gapZero
        _ = selected + -selected :=
          ((Arithmetic.add_comm selected (-selected)).trans
            (Arithmetic.neg_add_cancel selected)).symm
    rw [competitorSelected]
  · have productNonnegative : 0 ≤ gap * (gap - 2 * error) := by
      rcases Order.lt_or_gt_of_ne gapZero with gapNegative | gapPositive
      · have gapAtMostMinusOne : gapInt ≤ -1 := by
          change gapInt + 1 ≤ (0 : Int) at gapNegative
          have translated := Order.add_le_add gapNegative (Order.le_refl (-1))
          rw [Arithmetic.add_assoc, show (1 : Int) + -1 = 0 by decide,
            Int.add_zero, Arithmetic.zero_add] at translated
          exact translated
        have gapCastAtMostMinusOne : gap ≤ (-1 : Fraction.Rational) := by
          exact
            (Fraction.Cast.Order.intCast_le_intCast_iff_direct
              gapInt (-1)).2 gapAtMostMinusOne
        have minusOneLeTwiceError : (-1 : Fraction.Rational) ≤ 2 * error := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              errorLower (show (0 : Fraction.Rational) ≤ 2 by decide)
          calc
            (-1 : Fraction.Rational) = 2 * (-(1 / 2 : Fraction.Rational)) := by decide
            _ ≤ 2 * error := scaled
        have gapLeTwiceError : gap ≤ 2 * error :=
          gapCastAtMostMinusOne.trans minusOneLeTwiceError
        have gapNonpositive : gap ≤ 0 :=
          gapCastAtMostMinusOne.trans (show (-1 : Fraction.Rational) ≤ 0 by decide)
        have factorNonpositive : gap - 2 * error ≤ 0 := by
          have translated :=
            Fraction.Order.Arithmetic.add_le_add_right_direct gapLeTwiceError
              (-(2 * error))
          calc
            gap - 2 * error = gap + -(2 * error) := by ring1
            _ ≤ 2 * error + -(2 * error) := translated
            _ = 0 := by ring1
        have negativeGapNonnegative : 0 ≤ -gap := by
          calc
            0 ≤ 0 - gap :=
              Fraction.Order.Arithmetic.sub_nonneg_direct gapNonpositive
            _ = -gap := by ring1
        have negativeFactorNonnegative : 0 ≤ -(gap - 2 * error) := by
          calc
            0 ≤ 0 - (gap - 2 * error) :=
              Fraction.Order.Arithmetic.sub_nonneg_direct factorNonpositive
            _ = -(gap - 2 * error) := by ring1
        have product := Fraction.Order.Arithmetic.mul_nonneg_direct
          negativeGapNonnegative negativeFactorNonnegative
        calc
          0 ≤ (-gap) * (-(gap - 2 * error)) := product
          _ = gap * (gap - 2 * error) := by ring1
      · have oneLeGapInt : (1 : Int) ≤ gapInt := by
          change (1 : Int) ≤ gapInt at gapPositive
          exact gapPositive
        have oneLeGap : (1 : Fraction.Rational) ≤ gap := by
          exact
            (Fraction.Cast.Order.intCast_le_intCast_iff_direct
              1 gapInt).2 oneLeGapInt
        have twiceErrorLtOne : 2 * error < (1 : Fraction.Rational) := by
          have scaled :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (show (0 : Fraction.Rational) < 2 by decide) errorUpper
          calc
            2 * error < 2 * (1 / 2 : Fraction.Rational) := scaled
            _ = 1 := by decide
        have twiceErrorLeGap : 2 * error ≤ gap :=
          twiceErrorLtOne.le.trans oneLeGap
        have gapNonnegative : 0 ≤ gap :=
          (show (0 : Fraction.Rational) ≤ 1 by decide).trans oneLeGap
        exact Fraction.Order.Arithmetic.mul_nonneg_direct gapNonnegative
          (Fraction.Order.Arithmetic.sub_nonneg_direct twiceErrorLeGap)
    have differenceNonnegative :
        0 ≤ (value - (competitor : Fraction.Rational)) ^ 2 - error ^ 2 := by
      calc
        0 ≤ gap * (gap - 2 * error) := productNonnegative
        _ = (value - (competitor : Fraction.Rational)) ^ 2 - error ^ 2 := by
          dsimp only [gap, gapInt, error, selected]
          rw [IntCast.sub]
          ring1
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      differenceNonnegative (error ^ 2)
    change error ^ 2 ≤ (value - (competitor : Fraction.Rational)) ^ 2
    calc
      error ^ 2 = 0 + error ^ 2 := by ring1
      _ ≤ ((value - (competitor : Fraction.Rational)) ^ 2 - error ^ 2) +
          error ^ 2 := shifted
      _ = (value - (competitor : Fraction.Rational)) ^ 2 := by ring1
end Purelib.Data.Rat.Rounding.Nearest

end
