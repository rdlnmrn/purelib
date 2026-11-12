module

public import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Positive parameter increments preserving Legendre regularity

The original distances from zero and one give one positive allocation
for squared increments. Both exact shifted distances retain a quarter
of their original floors, constructing genuine target parameter clearance
without assuming either singular-value exclusion.
-/

public section

namespace Purelib.Curves.Legendre.PicardFuchs.Clearance.ParameterClearance

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds

variable {parameter : Canonical} (clearance : ParameterClearance parameter)

/-- The original two singular-value distance floors give one positive squared parameter-increment allocation. -/
@[expose] def incrementBound : Rational := min clearance.zeroBound clearance.oneBound / 4

/-- Both original singular-value exclusions make the computed increment allocation strictly positive. -/
theorem incrementBound_positive : 0 < clearance.incrementBound :=
  Quarter.quarter_pos (Order.Basic.lt_min clearance.zeroPositive clearance.onePositive)

/-- The computed parameter increment pays a quarter of the original zero-distance floor. -/
theorem incrementBound_le_zero : clearance.incrementBound ≤ clearance.zeroBound / 4 :=
  Order.Field.divide_mono (Order.Basic.min_le_left _ _) (by decide +kernel)

/-- The identical computed increment also pays a quarter of the original one-distance floor. -/
theorem incrementBound_le_one : clearance.incrementBound ≤ clearance.oneBound / 4 :=
  Order.Field.divide_mono (Order.Basic.min_le_right _ _) (by decide +kernel)

/-- An admitted exact parameter increment retains one quarter of the original zero-distance floor. -/
theorem shifted_zero_lower (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    clearance.zeroBound / 4 ≤ Norm.Basic.normSq (parameter + increment) := by
  have floor := Order.Field.divide_mono clearance.zeroLower (by decide +kernel : (0 : Rational) < 4)
  have movement : Norm.Basic.normSq (parameter - (parameter + increment)) ≤ Norm.Basic.normSq parameter / 4 := by
    rewrite [show parameter - (parameter + increment) = -increment by ring1, Norm.Basic.normSq_neg]
    exact admitted.trans (clearance.incrementBound_le_zero.trans floor)
  exact floor.trans (Norm.Bounds.quarter_normSq_le_of_close parameter (parameter + increment) movement)

/-- The same admitted increment retains one quarter of the original distance floor from parameter one. -/
theorem shifted_one_lower (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    clearance.oneBound / 4 ≤ Norm.Basic.normSq (parameter + increment - 1) := by
  have floor := Order.Field.divide_mono clearance.oneLower (by decide +kernel : (0 : Rational) < 4)
  have movement : Norm.Basic.normSq ((parameter - 1) - (parameter + increment - 1)) ≤
      Norm.Basic.normSq (parameter - 1) / 4 := by
    rewrite [show (parameter - 1) - (parameter + increment - 1) = -increment by ring1, Norm.Basic.normSq_neg]
    exact admitted.trans (clearance.incrementBound_le_one.trans floor)
  exact floor.trans (Norm.Bounds.quarter_normSq_le_of_close (parameter - 1) (parameter + increment - 1) movement)

/-- Construct clearance for the identical shifted parameter from the original finite increment payment.

The original positive floors are quartered, and their two lower bounds
are derived from the actual increment. Both target singular-value
exclusions are consequences of this certificate, rather than inputs.
-/
def shifted (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    ParameterClearance (parameter + increment) :=
  { zeroBound := clearance.zeroBound / 4
    zeroPositive := Quarter.quarter_pos clearance.zeroPositive
    zeroLower := clearance.shifted_zero_lower increment admitted
    oneBound := clearance.oneBound / 4
    onePositive := Quarter.quarter_pos clearance.onePositive
    oneLower := clearance.shifted_one_lower increment admitted }

/-- The shifted certificate retains a quarter of the identical original zero-distance floor. -/
theorem shifted_zeroBound (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    (clearance.shifted increment admitted).zeroBound = clearance.zeroBound / 4 := by
  rfl

/-- The shifted certificate retains a quarter of the identical original one-distance floor. -/
theorem shifted_oneBound (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    (clearance.shifted increment admitted).oneBound = clearance.oneBound / 4 := by
  rfl

end Purelib.Curves.Legendre.PicardFuchs.Clearance.ParameterClearance

end
