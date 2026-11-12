module

public import Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Fixed scalar ceilings for original nonlinear inverse-root factors

The original radicand certificate and slope budget remain unchanged. Upper
bounds on their actual retained scalar factors, together with the same positive
root and signed-sum floors, bound the existing inverse factor monotonically.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The fixed error ceiling retains both original square-residual factors and the radicand remainder ceiling. -/
@[expose] def errorCeiling (factor firstFactor lastFactor : Fraction.Rational) : Fraction.Rational :=
  2 * (factor + 2 * (firstFactor + lastFactor))

/-- The fixed movement ceiling uses the original signed-sum floor and radicand slope ceiling. -/
@[expose] def movementCeiling (factor slope sumFloor firstFactor lastFactor : Fraction.Rational) : Fraction.Rational :=
  2 * (slope + errorCeiling factor firstFactor lastFactor) * sumFloor⁻¹

/-- The positive original denominator floor pays the fixed nonlinear root-remainder ceiling. -/
@[expose] def remainderCeiling (factor slope floor sumFloor firstFactor lastFactor : Fraction.Rational) :
    Fraction.Rational :=
  2 * (errorCeiling factor firstFactor lastFactor +
    movementCeiling factor slope sumFloor firstFactor lastFactor ^ 2) * floor⁻¹

/-- The same original inverse and sensitivity factors give the fixed nonlinear reciprocal-root ceiling. -/
@[expose] def inverseCeiling (factor slope floor sumFloor firstFactor lastFactor : Fraction.Rational) :
    Fraction.Rational :=
  let root := remainderCeiling factor slope floor sumFloor firstFactor lastFactor
  2 * (floor⁻¹ ^ 2 * root + floor⁻¹ ^ 3 * (2 * (slope * floor⁻¹ + root)) ^ 2)

/-- A positive original denominator floor and nonnegative residual budgets make the inverse ceiling nonnegative.

The retained movement and reciprocal-sensitivity expressions enter as
squares. Their values do not need additional sign assumptions; the displayed
radicand and two square-residual budgets pay the remaining error term.
-/
theorem inverseCeiling_nonnegative {factor slope floor sumFloor firstFactor lastFactor : Fraction.Rational}
    (factorNonnegative : 0 ≤ factor) (floorPositive : 0 < floor)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    0 ≤ inverseCeiling factor slope floor sumFloor firstFactor lastFactor := by
  have floorInverse := (Fraction.Order.Field.inv_pos_direct floorPositive).le
  have errorNonnegative : 0 ≤ errorCeiling factor firstFactor lastFactor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct factorNonnegative
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative)))
  have rootNonnegative : 0 ≤ remainderCeiling factor slope floor sumFloor firstFactor lastFactor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct errorNonnegative
          (Arithmetic.sq_nonneg_direct
            (movementCeiling factor slope sumFloor firstFactor lastFactor)))) floorInverse
  unfold inverseCeiling
  exact Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.pow_nonneg_direct floorInverse 2) rootNonnegative)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.pow_nonneg_direct floorInverse 3)
        (Arithmetic.sq_nonneg_direct
          (2 * (slope * floor⁻¹ + remainderCeiling factor slope floor sumFloor firstFactor lastFactor)))))

/-- Fixed radicand and slope ceilings bound the existing actual nonlinear inverse-root factor.

Both original residual factors and positive denominator/sum floors remain
the same inputs of the actual factor. Direct scalar monotonicity pays each
error, movement, root-remainder and reciprocal sensitivity term.
-/
theorem inverseFactor_le_ceiling {increment : Canonical} (radicand : Certificate increment)
    {firstFactor lastFactor slopeUpper factorCeiling slopeCeiling floor sumFloor : Fraction.Rational}
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) (slopeNonnegative : 0 ≤ slopeUpper)
    (floorPositive : 0 < floor) (sumPositive : 0 < sumFloor)
    (factorBound : radicand.factor ≤ factorCeiling) (slopeBound : slopeUpper ≤ slopeCeiling) :
    inverseFactor radicand firstFactor lastFactor slopeUpper floor sumFloor ≤
      inverseCeiling factorCeiling slopeCeiling floor sumFloor firstFactor lastFactor := by
  have floorInverse := (Fraction.Order.Field.inv_pos_direct floorPositive).le
  have sumInverse := (Fraction.Order.Field.inv_pos_direct sumPositive).le
  have errorBound : errorFactor radicand firstFactor lastFactor ≤
      errorCeiling factorCeiling firstFactor lastFactor :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct factorBound
        (Fraction.Order.Basic.le_refl (2 * (firstFactor + lastFactor)))) (by decide +kernel)
  have errorNonnegative := errorFactor_nonnegative radicand firstNonnegative lastNonnegative
  have movementBound : movementFactor radicand firstFactor lastFactor slopeUpper sumFloor ≤
      movementCeiling factorCeiling slopeCeiling sumFloor firstFactor lastFactor :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct slopeBound errorBound) (by decide +kernel)) sumInverse
  have movementNonnegative : 0 ≤ movementFactor radicand firstFactor lastFactor slopeUpper sumFloor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct slopeNonnegative errorNonnegative)) sumInverse
  have rootBound : remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor ≤
      remainderCeiling factorCeiling slopeCeiling floor sumFloor firstFactor lastFactor :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct errorBound
          (Arithmetic.pow_le_pow_direct movementNonnegative movementBound 2))
        (by decide +kernel)) floorInverse
  have rootNonnegative : 0 ≤ remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct errorNonnegative
          (Arithmetic.sq_nonneg_direct
            (movementFactor radicand firstFactor lastFactor slopeUpper sumFloor)))) floorInverse
  have sensitivityBound :
      2 * (slopeUpper * floor⁻¹ + remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor) ≤
        2 * (slopeCeiling * floor⁻¹ +
          remainderCeiling factorCeiling slopeCeiling floor sumFloor firstFactor lastFactor) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct slopeBound floorInverse) rootBound)
      (by decide +kernel)
  have sensitivityNonnegative :
      0 ≤ 2 * (slopeUpper * floor⁻¹ + remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct slopeNonnegative floorInverse) rootNonnegative)
  have first := Arithmetic.mul_le_mul_of_nonneg_left_direct rootBound
    (Arithmetic.pow_nonneg_direct floorInverse 2)
  have last := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct sensitivityNonnegative sensitivityBound 2)
    (Arithmetic.pow_nonneg_direct floorInverse 3)
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct first last) (by decide +kernel)

end Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand

end
