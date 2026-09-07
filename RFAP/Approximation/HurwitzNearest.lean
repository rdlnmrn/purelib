import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussianHeight

/-!
# Constructive nearest-Gaussian-integer arithmetic

This is the finite arithmetic kernel for a Hurwitz continued fraction over
the Gaussian integers.  Ties are resolved coordinatewise toward the positive
integer: `nearestCoordinate x = floor (x + 1/2)`.  Consequently the displayed
remainder lies in the half-open square `[-1/2, 1/2)²` and has quadrance at
most `1/2`.
-/

namespace RFAP.HurwitzNearest

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- Deterministic nearest integer, with a half-integer tie sent upward. -/
def nearestCoordinate (value : Coordinate) : Int :=
  RFAP.ConstructiveFraction.floor (value + 1 / 2)

/-- Deterministic nearest Gaussian integer, independently in both
coordinates. -/
def nearest (value : Gaussian) : GaussianInt :=
  ⟨nearestCoordinate value.re, nearestCoordinate value.im⟩

/-- The residual after subtracting the selected nearest Gaussian integer. -/
def remainder (value : Gaussian) : Gaussian :=
  value - toGaussian (nearest value)

/-- The half-open fundamental square used by the deterministic tie rule. -/
def InFundamentalSquare (value : Gaussian) : Prop :=
  -(1 / 2 : Coordinate) ≤ value.re ∧ value.re < 1 / 2 ∧
    -(1 / 2 : Coordinate) ≤ value.im ∧ value.im < 1 / 2

private theorem intCast_floor_le (value : Coordinate) :
    ((RFAP.ConstructiveFraction.floor value : Int) : Coordinate) ≤ value :=
  (RFAP.ConstructiveFraction.intCast_le_iff_floor _ _).2 le_rfl

private theorem lt_intCast_floor_add_one (value : Coordinate) :
    value <
      ((RFAP.ConstructiveFraction.floor value + 1 : Int) : Coordinate) := by
  apply lt_of_not_ge
  intro reverse
  have impossible :=
    (RFAP.ConstructiveFraction.intCast_le_iff_floor
      (RFAP.ConstructiveFraction.floor value + 1) value).1 reverse
  exact (Int.not_le_of_gt
    (Int.lt_add_one_iff.mpr (show
      RFAP.ConstructiveFraction.floor value ≤
        RFAP.ConstructiveFraction.floor value from le_rfl)) impossible).elim

theorem nearestCoordinate_error_bounds (value : Coordinate) :
    -(1 / 2 : Coordinate) ≤
        value - (nearestCoordinate value : Coordinate) ∧
      value - (nearestCoordinate value : Coordinate) < 1 / 2 := by
  let shifted := value + (1 / 2 : Coordinate)
  let selected := RFAP.ConstructiveFraction.floor shifted
  have selectedLower : (selected : Coordinate) ≤ shifted := by
    exact intCast_floor_le shifted
  have selectedUpper :
      shifted < ((selected + 1 : Int) : Coordinate) := by
    exact lt_intCast_floor_add_one shifted
  have lowerBase : (selected : Coordinate) - 1 / 2 ≤ value := by
    calc
      (selected : Coordinate) - 1 / 2 ≤ shifted - 1 / 2 :=
        RFAP.ConstructiveFraction.add_le_add_right_direct selectedLower
          (-(1 / 2 : Coordinate))
      _ = value := by
        dsimp only [shifted]
        ring1
  have lowerShifted :=
    RFAP.ConstructiveFraction.add_le_add_right_direct lowerBase
      (-(selected : Coordinate))
  have upperBase : value < (selected : Coordinate) + 1 / 2 := by
    have translated :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct selectedUpper
        (-(1 / 2 : Coordinate))
    calc
      value = shifted - 1 / 2 := by
        dsimp only [shifted]
        ring1
      _ < (((selected + 1 : Int) : Coordinate) - 1 / 2) := translated
      _ = (selected : Coordinate) + 1 / 2 := by
        rw [Int.cast_add, Int.cast_one]
        calc
          (selected : Coordinate) + 1 - 1 / 2 =
              (selected : Coordinate) + (1 - 1 / 2) := by ring1
          _ = (selected : Coordinate) + 1 / 2 := by
            rw [show (1 : Coordinate) - 1 / 2 = 1 / 2 by decide]
  have upperShifted :=
    RFAP.ConstructiveFraction.add_lt_add_right_direct upperBase
      (-(selected : Coordinate))
  change
    -(1 / 2 : Coordinate) ≤
        value - (RFAP.ConstructiveFraction.floor
          (value + 1 / 2) : Coordinate) ∧
      value - (RFAP.ConstructiveFraction.floor
        (value + 1 / 2) : Coordinate) < 1 / 2
  constructor
  · change
      -(1 / 2 : Coordinate) ≤ value - (selected : Coordinate)
    calc
      -(1 / 2 : Coordinate) =
          ((selected : Coordinate) - 1 / 2) - selected := by ring1
      _ ≤ value - selected := lowerShifted
  · change value - (selected : Coordinate) < (1 / 2 : Coordinate)
    calc
      value - (selected : Coordinate) <
          ((selected : Coordinate) + 1 / 2) - selected := upperShifted
      _ = 1 / 2 := by ring1

/-- The computed nearest-Gaussian-integer remainder belongs to the chosen
half-open fundamental square. -/
theorem remainder_mem (value : Gaussian) :
    InFundamentalSquare (remainder value) := by
  have realBounds := nearestCoordinate_error_bounds value.re
  have imaginaryBounds := nearestCoordinate_error_bounds value.im
  exact ⟨realBounds.1, realBounds.2, imaginaryBounds.1, imaginaryBounds.2⟩

private theorem square_le_quarter {value : Coordinate}
    (lower : -(1 / 2 : Coordinate) ≤ value)
    (upper : value < 1 / 2) :
    value ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 := by
  have leftNonnegative :
      0 ≤ (1 / 2 : Coordinate) - value :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upper.le
  have rightNonnegative :
      0 ≤ value + (1 / 2 : Coordinate) := by
    have translated :=
      RFAP.ConstructiveFraction.add_le_add_right_direct lower
        (1 / 2 : Coordinate)
    calc
      0 = -(1 / 2 : Coordinate) + 1 / 2 := by ring1
      _ ≤ value + 1 / 2 := translated
  have productNonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
    leftNonnegative rightNonnegative
  have differenceNonnegative :
      0 ≤ (1 / 2 : Coordinate) ^ 2 - value ^ 2 := by
    calc
      0 ≤ ((1 / 2 : Coordinate) - value) * (value + 1 / 2) :=
        productNonnegative
      _ = (1 / 2 : Coordinate) ^ 2 - value ^ 2 := by ring1
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    differenceNonnegative (value ^ 2)
  calc
    value ^ 2 = 0 + value ^ 2 := by ring1
    _ ≤ ((1 / 2 : Coordinate) ^ 2 - value ^ 2) + value ^ 2 := shifted
    _ = (1 / 2 : Coordinate) ^ 2 := by ring1

/-- The nearest-Gaussian-integer residual has quadrance at most one half. -/
theorem remainder_normSq_le_half (value : Gaussian) :
    normSq (remainder value) ≤ 1 / 2 := by
  have inside := remainder_mem value
  have realBound := square_le_quarter inside.1 inside.2.1
  have imaginaryBound := square_le_quarter inside.2.2.1 inside.2.2.2
  calc
    normSq (remainder value) =
        (remainder value).re ^ 2 + (remainder value).im ^ 2 := rfl
    _ ≤ (1 / 2 : Coordinate) ^ 2 + (remainder value).im ^ 2 :=
      RFAP.ConstructiveFraction.add_le_add_right_direct realBound _
    _ ≤ (1 / 2 : Coordinate) ^ 2 + (1 / 2 : Coordinate) ^ 2 := by
      have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
        imaginaryBound ((1 / 2 : Coordinate) ^ 2)
      calc
        (1 / 2 : Coordinate) ^ 2 + (remainder value).im ^ 2 =
            (remainder value).im ^ 2 + (1 / 2 : Coordinate) ^ 2 :=
          _root_.add_comm _ _
        _ ≤ (1 / 2 : Coordinate) ^ 2 + (1 / 2 : Coordinate) ^ 2 := shifted
    _ = 1 / 2 := by decide

/-- Coordinatewise nearest-integer selection minimizes squared error against
every displayed integer competitor. -/
theorem nearestCoordinate_sq_le (value : Coordinate) (competitor : Int) :
    (value - (nearestCoordinate value : Coordinate)) ^ 2 ≤
      (value - (competitor : Coordinate)) ^ 2 := by
  let selected := nearestCoordinate value
  let error : Coordinate := value - (selected : Coordinate)
  let gapInt : Int := competitor - selected
  let gap : Coordinate := (gapInt : Coordinate)
  have bounds := nearestCoordinate_error_bounds value
  have errorLower : -(1 / 2 : Coordinate) ≤ error := by
    exact bounds.1
  have errorUpper : error < 1 / 2 := by
    exact bounds.2
  by_cases gapZero : gapInt = 0
  · have competitorSelected : competitor = selected := by
      dsimp only [gapInt] at gapZero
      exact Int.sub_eq_zero.mp gapZero
    rw [competitorSelected]
  · have productNonnegative : 0 ≤ gap * (gap - 2 * error) := by
      rcases lt_or_gt_of_ne gapZero with gapNegative | gapPositive
      · have gapAtMostMinusOne : gapInt ≤ -1 := by
          change gapInt ≤ (0 : Int) - 1
          exact Int.le_sub_one_iff.mpr gapNegative
        have gapCastAtMostMinusOne : gap ≤ (-1 : Coordinate) := by
          exact
            (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
              gapInt (-1)).2 gapAtMostMinusOne
        have minusOneLeTwiceError : (-1 : Coordinate) ≤ 2 * error := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              errorLower (show (0 : Coordinate) ≤ 2 by decide)
          calc
            (-1 : Coordinate) = 2 * (-(1 / 2 : Coordinate)) := by decide
            _ ≤ 2 * error := scaled
        have gapLeTwiceError : gap ≤ 2 * error :=
          gapCastAtMostMinusOne.trans minusOneLeTwiceError
        have gapNonpositive : gap ≤ 0 :=
          gapCastAtMostMinusOne.trans (show (-1 : Coordinate) ≤ 0 by decide)
        have factorNonpositive : gap - 2 * error ≤ 0 := by
          have translated :=
            RFAP.ConstructiveFraction.add_le_add_right_direct gapLeTwiceError
              (-(2 * error))
          calc
            gap - 2 * error = gap + -(2 * error) := by ring1
            _ ≤ 2 * error + -(2 * error) := translated
            _ = 0 := by ring1
        have negativeGapNonnegative : 0 ≤ -gap := by
          calc
            0 ≤ 0 - gap :=
              RFAP.ConstructiveFraction.sub_nonneg_direct gapNonpositive
            _ = -gap := by ring1
        have negativeFactorNonnegative : 0 ≤ -(gap - 2 * error) := by
          calc
            0 ≤ 0 - (gap - 2 * error) :=
              RFAP.ConstructiveFraction.sub_nonneg_direct factorNonpositive
            _ = -(gap - 2 * error) := by ring1
        have product := RFAP.ConstructiveFraction.mul_nonneg_direct
          negativeGapNonnegative negativeFactorNonnegative
        calc
          0 ≤ (-gap) * (-(gap - 2 * error)) := product
          _ = gap * (gap - 2 * error) := by ring1
      · have oneLeGapInt : (1 : Int) ≤ gapInt := by
          change (0 : Int) + 1 ≤ gapInt
          exact Int.add_one_le_iff.mpr gapPositive
        have oneLeGap : (1 : Coordinate) ≤ gap := by
          exact
            (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
              1 gapInt).2 oneLeGapInt
        have twiceErrorLtOne : 2 * error < (1 : Coordinate) := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (show (0 : Coordinate) < 2 by decide) errorUpper
          calc
            2 * error < 2 * (1 / 2 : Coordinate) := scaled
            _ = 1 := by decide
        have twiceErrorLeGap : 2 * error ≤ gap :=
          twiceErrorLtOne.le.trans oneLeGap
        have gapNonnegative : 0 ≤ gap :=
          (show (0 : Coordinate) ≤ 1 by decide).trans oneLeGap
        exact RFAP.ConstructiveFraction.mul_nonneg_direct gapNonnegative
          (RFAP.ConstructiveFraction.sub_nonneg_direct twiceErrorLeGap)
    have differenceNonnegative :
        0 ≤ (value - (competitor : Coordinate)) ^ 2 - error ^ 2 := by
      calc
        0 ≤ gap * (gap - 2 * error) := productNonnegative
        _ = (value - (competitor : Coordinate)) ^ 2 - error ^ 2 := by
          dsimp only [gap, gapInt, error, selected]
          rw [Int.cast_sub]
          ring1
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      differenceNonnegative (error ^ 2)
    change error ^ 2 ≤ (value - (competitor : Coordinate)) ^ 2
    calc
      error ^ 2 = 0 + error ^ 2 := by ring1
      _ ≤ ((value - (competitor : Coordinate)) ^ 2 - error ^ 2) +
          error ^ 2 := shifted
      _ = (value - (competitor : Coordinate)) ^ 2 := by ring1

/-- The selected nearest Gaussian integer minimizes residual quadrance against
every displayed Gaussian-integer competitor. -/
theorem remainder_normSq_le_competitor (value : Gaussian)
    (competitor : GaussianInt) :
    normSq (remainder value) ≤ normSq (value - toGaussian competitor) := by
  have realBound := nearestCoordinate_sq_le value.re competitor.re
  have imaginaryBound := nearestCoordinate_sq_le value.im competitor.im
  change
    (value.re - (nearestCoordinate value.re : Coordinate)) ^ 2 +
        (value.im - (nearestCoordinate value.im : Coordinate)) ^ 2 ≤
      (value.re - (competitor.re : Coordinate)) ^ 2 +
        (value.im - (competitor.im : Coordinate)) ^ 2
  calc
    (value.re - (nearestCoordinate value.re : Coordinate)) ^ 2 +
        (value.im - (nearestCoordinate value.im : Coordinate)) ^ 2 ≤
      (value.re - (competitor.re : Coordinate)) ^ 2 +
        (value.im - (nearestCoordinate value.im : Coordinate)) ^ 2 :=
      RFAP.ConstructiveFraction.add_le_add_right_direct realBound _
    _ ≤ (value.re - (competitor.re : Coordinate)) ^ 2 +
        (value.im - (competitor.im : Coordinate)) ^ 2 := by
      have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
        imaginaryBound ((value.re - (competitor.re : Coordinate)) ^ 2)
      calc
        (value.re - (competitor.re : Coordinate)) ^ 2 +
            (value.im - (nearestCoordinate value.im : Coordinate)) ^ 2 =
          (value.im - (nearestCoordinate value.im : Coordinate)) ^ 2 +
            (value.re - (competitor.re : Coordinate)) ^ 2 :=
          _root_.add_comm _ _
        _ ≤ (value.im - (competitor.im : Coordinate)) ^ 2 +
            (value.re - (competitor.re : Coordinate)) ^ 2 := shifted
        _ = (value.re - (competitor.re : Coordinate)) ^ 2 +
            (value.im - (competitor.im : Coordinate)) ^ 2 :=
          _root_.add_comm _ _

end RFAP.HurwitzNearest
