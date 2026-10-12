module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Lp.Comparison
import Purelib.Measure.Distribution.Lp.Geometry
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Regression.Linear
import Purelib.Data.Rat.Fraction

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Coin.Basic

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples

/-- The Boolean probability distribution assigning mass one half to each outcome. -/
def fairCoin : Distribution Bool where
  atoms :=
    [⟨false, 1 / 2, by decide⟩,
      ⟨true, 1 / 2, by decide⟩]
  total_one := by decide

/-- The rational indicator of the true coin outcome. -/
def coinNumber (outcome : Bool) : Fraction.Rational :=
  if outcome then 1 else 0

/-- The rational indicator of the false coin outcome. -/
def reverseCoinNumber (outcome : Bool) : Fraction.Rational :=
  if outcome then 0 else 1

/-- The true indicator has squared L2 value one half. -/
example : fairCoin.poweredL2 coinNumber = 1 / 2 := by
  decide

/-- The false indicator has squared L2 value one half. -/
example : fairCoin.poweredL2 reverseCoinNumber = 1 / 2
  := by
  decide

/-- The two coin indicators satisfy the squared-L2 parallelogram identity. -/
example : fairCoin.poweredL2
        (fun outcome => coinNumber outcome +
          reverseCoinNumber outcome) +
      fairCoin.poweredL2
        (fun outcome => coinNumber outcome -
          reverseCoinNumber outcome) =
    2 * (fairCoin.poweredL2 coinNumber +
      fairCoin.poweredL2 reverseCoinNumber) :=
  fairCoin.poweredL2_add_sub coinNumber
    reverseCoinNumber

/-- The displayed sum of squared-L2 values of the sum and difference equals two. -/
example : fairCoin.poweredL2
        (fun outcome => coinNumber outcome +
          reverseCoinNumber outcome) +
      fairCoin.poweredL2
        (fun outcome => coinNumber outcome -
          reverseCoinNumber outcome) =
    2 := by
  decide

/-- The displayed squared-L2 distances satisfy the factor-two triangle bound. -/
example : fairCoin.poweredL2Distance coinNumber (fun _
  => 0) ≤
    2 * (fairCoin.poweredL2Distance coinNumber
      reverseCoinNumber +
      fairCoin.poweredL2Distance reverseCoinNumber (fun
        _ => 0)) :=
  fairCoin.poweredL2Distance_le_two_mul_add
    coinNumber reverseCoinNumber (fun _ => 0)

/-- The cubed-Lp value of the indicator sum satisfies the factor-eight bound. -/
example : fairCoin.poweredLp 3
      (fun outcome => coinNumber outcome +
        reverseCoinNumber outcome) ≤
    (2 : Fraction.Rational) ^ 3 *
      (fairCoin.poweredLp 3 coinNumber +
        fairCoin.poweredLp 3 reverseCoinNumber) :=
  fairCoin.poweredLp_add_le_two_pow_mul 3
    coinNumber reverseCoinNumber

/-- The displayed cubed-Lp distances satisfy the factor-eight triangle bound. -/
example : fairCoin.poweredLpDistance 3 coinNumber (fun _
  => 0) ≤
    (2 : Fraction.Rational) ^ 3 *
      (fairCoin.poweredLpDistance 3 coinNumber
        reverseCoinNumber +
        fairCoin.poweredLpDistance 3 reverseCoinNumber
          (fun _ => 0)) :=
  fairCoin.poweredLpDistance_le_two_pow_mul 3
    coinNumber reverseCoinNumber (fun _ => 0)

/-- The zeroth powered-Lp value of the coin indicator is one. -/
example : fairCoin.poweredLp 0 coinNumber = 1 :=
  fairCoin.poweredLp_zero coinNumber

/-- The first powered-Lp value of the coin indicator equals its L1 value. -/
example : fairCoin.poweredLp 1 coinNumber =
  fairCoin.poweredL1 coinNumber :=
  fairCoin.poweredLp_one coinNumber

/-- The second powered-Lp value of the coin indicator equals its squared L2 value. -/
example : fairCoin.poweredLp 2 coinNumber =
  fairCoin.poweredL2 coinNumber :=
  fairCoin.poweredLp_two coinNumber

/-- The squared L2 value of the indicator is bounded by its essential maximum times its L1 value. -/
example : fairCoin.poweredL2 coinNumber ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.poweredL1 coinNumber :=
  fairCoin.poweredL2_le_essentialMaximum_mul_poweredL1
    coinNumber

/-- The squared L1 value of the coin indicator is bounded by its squared L2 value. -/
example : fairCoin.poweredL1 coinNumber ^ 2 ≤
    fairCoin.poweredL2 coinNumber :=
  fairCoin.poweredL1_sq_le_poweredL2 coinNumber

/-- The indicator has squared L1 value one quarter and squared L2 value one half. -/
example : fairCoin.poweredL1 coinNumber ^ 2 = 1 / 4 ∧
    fairCoin.poweredL2 coinNumber = 1 / 2 := by
  decide

/-- The squared L1 distance of the two indicators is bounded by their squared L2 distance. -/
example : fairCoin.l1Distance coinNumber
  reverseCoinNumber ^ 2 ≤
    fairCoin.poweredL2Distance coinNumber
      reverseCoinNumber :=
  fairCoin.l1Distance_sq_le_poweredL2Distance
    coinNumber reverseCoinNumber

/-- The indicator attains the essential-maximum-times-L1 bound at one half. -/
example : fairCoin.poweredL2 coinNumber = 1 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.poweredL1 coinNumber = 1 / 2 := by
  decide

/-- The squared L2 distance is bounded by essential maximum difference times L1 distance. -/
example : fairCoin.poweredL2Distance coinNumber
  reverseCoinNumber ≤
    fairCoin.essentialMaximumMagnitude
        (fun outcome => coinNumber outcome -
          reverseCoinNumber outcome) *
      fairCoin.l1Distance coinNumber
        reverseCoinNumber :=
  fairCoin.poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    coinNumber reverseCoinNumber

/-- The two coin indicators attain the displayed L2-distance bound at one. -/
example : fairCoin.poweredL2Distance coinNumber
  reverseCoinNumber = 1 ∧
    fairCoin.essentialMaximumMagnitude
        (fun outcome => coinNumber outcome -
          reverseCoinNumber outcome) *
      fairCoin.l1Distance coinNumber
        reverseCoinNumber = 1 := by
  decide

/-- The displayed coin payoff equal to three on true and one on false. -/
def coinPayoff (outcome : Bool) : Fraction.Rational :=
  if outcome then 3 else 1

/-- Regressing the displayed payoff on the true indicator has slope two. -/
example : fairCoin.regressionSlope coinNumber
  coinPayoff = 2 := by
  decide

/-- The linear prediction from the true indicator equals the displayed payoff at both outcomes. -/
example : fairCoin.linearPrediction coinNumber
  coinPayoff = coinPayoff := by
  funext outcome
  cases outcome <;> decide

/-- The displayed payoff variance splits into prediction variance and residual variance. -/
example : fairCoin.variance coinPayoff =
    fairCoin.variance (fairCoin.linearPrediction
      coinNumber coinPayoff) +
      fairCoin.variance (fairCoin.regressionResidual
        coinNumber coinPayoff) :=
  fairCoin.variance_eq_linearPrediction_add_regressionResidual
    coinNumber coinPayoff (by decide)

end Purelib.Examples.Measure.Distribution.Coin.Basic

end
