module
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Tactic.Ring

public section

/-! A full noisy side-area bound has quadratic radius decay even when its
Newton density grows inversely with radius. No subdivision count enters the
coefficient; the canonical budget pays every zero-displacement junction. -/
namespace Purelib.Riemann.RootContinuation.NewtonAreaRate

open Purelib.Data.Rat

open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget (build)

namespace LengthErrorBudget

open Purelib.Integration
open Purelib.Data
/-- The canonical length-error padding is at most its positive radius. -/
theorem build_padding_le (count : Nat) {radius : Coordinate} (positive : 0 < radius) :
    (Path.NoisyPathArea.LengthErrorBudget.build count radius positive).padding ≤ radius := by
  change radius / ((count : Coordinate) + 1) ≤ radius
  have nonnegative : (0 : Coordinate) ≤ count := Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  apply (Rat.Fraction.Order.Field.div_le_iff_pos (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    nonnegative (by decide +kernel))).mpr
  have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (by
      calc
        (1 : Coordinate) = 0 + 1 := by ring1
        _ ≤ (count : Coordinate) + 1 :=
          Rat.Fraction.Order.Arithmetic.add_le_add_direct nonnegative (le_refl (1 : Coordinate))) positive.le
  simpa only [mul_one] using h

/-- Padding bounded by the radius gives a tolerance bounded by its square. -/
theorem tolerance_le_radius_sq {count : Nat} {radius : Coordinate}
    (budget : Path.NoisyPathArea.LengthErrorBudget count radius) (paddingLe : budget.padding ≤ radius) :
    budget.tolerance ≤ radius ^ 2 := by
  rw [budget.tolerance_eq]
  exact Rat.Fraction.Order.Arithmetic.pow_le_pow_direct budget.padding_positive.le paddingLe 2

end LengthErrorBudget

open Purelib.Data in
/-- The full noisy Newton side-area bound decays quadratically in radius.

For radius between zero and one, the hypotheses bound tolerance by radius squared, diagonal by 32 times radius squared,
length by four times radius, and density times radius by the rate. The resulting coefficient is independent of the
subdivision count. -/
theorem newton_area_rate {tolerance density diagonal length radius rate : Coordinate}
    (radiusNonnegative : 0 ≤ radius) (radiusLe : radius ≤ 1)
    (toleranceNonnegative : 0 ≤ tolerance) (toleranceLe : tolerance ≤ radius ^ 2)
    (densityNonnegative : 0 ≤ density) (densityRate : density * radius ≤ rate)
    (diagonalNonnegative : 0 ≤ diagonal) (diagonalLe : diagonal ≤ 32 * radius ^ 2)
    (lengthNonnegative : 0 ≤ length) (lengthLe : length ≤ 4 * radius) :
    4 * (3 * tolerance + 4 * density * diagonal) * (4 * density + 3) * (length + radius) ^ 2 ≤
      100 * (3 + 128 * rate) * (4 * rate + 3) * radius ^ 2 := by
  have rateNonnegative : 0 ≤ rate := (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
    radiusNonnegative).trans densityRate
  have magnitudeNonnegative : 0 ≤ 3 * tolerance + 4 * density * diagonal :=
    add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) toleranceNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide +kernel) densityNonnegative) diagonalNonnegative)
  have densityFactorNonnegative : 0 ≤ 4 * density + 3 :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) densityNonnegative) (by decide +kernel)
  have rateFactorNonnegative : 0 ≤ 3 + 128 * rate :=
    add_nonneg (by decide +kernel) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) rateNonnegative)
  have squareLe : radius ^ 2 ≤ radius := by
    have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLe radiusNonnegative
    simpa only [pow_two, mul_one] using h
  have densitySquare : density * radius ^ 2 ≤ rate * radius := by
    have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct densityRate radiusNonnegative
    exact (show density * radius ^ 2 = density * radius * radius by ring1) ▸ h
  have magnitude : 3 * tolerance + 4 * density * diagonal ≤ (3 + 128 * rate) * radius := by
    have first := Rat.Fraction.Order.Arithmetic.add_le_add_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct toleranceLe (by
          decide +kernel : (0 : Coordinate) ≤ 3))
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonalLe
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 4) densityNonnegative))
    have second := Rat.Fraction.Order.Arithmetic.add_le_add_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe (by
          decide +kernel : (0 : Coordinate) ≤ 3))
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct densitySquare (by
          decide +kernel : (0 : Coordinate) ≤ 128))
    calc
      _ ≤ 3 * radius ^ 2 + 4 * density * (32 * radius ^ 2) := first
      _ = 3 * radius ^ 2 + 128 * (density * radius ^ 2) := by ring1
      _ ≤ 3 * radius + 128 * (rate * radius) := second
      _ = _ := by ring1
  have densityFactor : (4 * density + 3) * radius ≤ 4 * rate + 3 := by
    have h := Rat.Fraction.Order.Arithmetic.add_le_add_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct densityRate (by
          decide +kernel : (0 : Coordinate) ≤ 4))
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLe (by
          decide +kernel : (0 : Coordinate) ≤ 3))
    calc
      _ = 4 * (density * radius) + 3 * radius := by ring1
      _ ≤ 4 * rate + 3 * 1 := h
      _ = _ := by ring1
  have lengthBound : (length + radius) ^ 2 ≤ 25 * radius ^ 2 := by
    have h := Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (add_nonneg lengthNonnegative radiusNonnegative)
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct lengthLe (le_refl radius)) 2
    exact h.trans_eq (by ring1)
  calc
    _ ≤ 4 * (3 * tolerance + 4 * density * diagonal) * (4 * density + 3) * (25 * radius ^ 2) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lengthBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
          (by decide +kernel) magnitudeNonnegative) densityFactorNonnegative)
    _ = (100 * (4 * density + 3) * radius ^ 2) * (3 * tolerance + 4 * density * diagonal) := by ring1
    _ ≤ (100 * (4 * density + 3) * radius ^ 2) * ((3 + 128 * rate) * radius) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct magnitude
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
          (by decide +kernel) densityFactorNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct radius))
    _ = (100 * (3 + 128 * rate) * radius ^ 2) * ((4 * density + 3) * radius) := by ring1
    _ ≤ (100 * (3 + 128 * rate) * radius ^ 2) * (4 * rate + 3) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct densityFactor
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
          (by decide +kernel) rateFactorNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct radius))
    _ = _ := by ring1

end Purelib.Riemann.RootContinuation.NewtonAreaRate
