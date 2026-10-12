module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Nat.SquareThreshold.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
public section

/-!
# Constructive small-residual samples with explicit denominator height

A selected Newton band contains a point on a computable square Gaussian grid.
Coordinatewise nearest-integer rounding halves the required mesh width: the
grid denominator is one more than the integer floor of `1 / (2r)`.  This gives
an exact finite denominator certificate for the box-to-residual estimate.
-/

namespace Purelib.Approximation.Rational.QuadraticTarget.Basic

open Purelib.Algebra

open Purelib

open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

/-- Natural denominator used for a quadratic residual request. It is the least positive natural whose square strictly
exceeds the ceiling of `coefficient / target`. -/
@[expose] def targetDenominator (coefficient target : Fraction.Rational) : Nat :=
  SquareThreshold.Basic.squareThreshold
    (Floor.ceilNat (coefficient / target))

/-- The computed quadratic-request denominator is a positive natural number. -/
theorem targetDenominator_pos (coefficient target : Fraction.Rational) :
    0 < Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target := by
  exact SquareThreshold.Basic.squareThreshold_pos _

/-- Rational request whose denominator grows at the square-root rate forced by a quadratic residual estimate. -/
@[expose] def targetEpsilon (coefficient target : Fraction.Rational) : Fraction.Rational :=
  1 / (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational)

/-- The reciprocal quadratic-request tolerance is strictly positive. -/
theorem targetEpsilon_pos (coefficient target : Fraction.Rational) :
    0 < Approximation.Rational.QuadraticTarget.Basic.targetEpsilon coefficient target := by
  exact Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Cast.Order.natCast_pos_direct
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator_pos coefficient target))

/-- The displayed ratio is strictly below the square of its computed least square threshold.

The certified natural square threshold is transported through the same rational cast; its strict bound applies to the
retained coefficient-to-target ratio. -/
theorem ratio_lt_targetDenominator_sq
    {coefficient target : Fraction.Rational} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient / target <
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 := by
  let ceiling := Floor.ceilNat (coefficient / target)
  have ratioNonnegative : (0 : Fraction.Rational) ≤ coefficient / target :=
    (Fraction.Order.Field.div_pos_direct coefficientPositive
      targetPositive).le
  have ratioLeCeiling : coefficient / target ≤ (ceiling : Fraction.Rational) := by
    exact Floor.le_natCast_ceilNat_of_nonneg
      ratioNonnegative
  have ceilingLtDenominatorSqNat :
      ceiling < SquareThreshold.Basic.squareThreshold ceiling * SquareThreshold.Basic.squareThreshold ceiling :=
    SquareThreshold.Basic.squareThreshold_spec ceiling
  have ceilingLtDenominatorSq :
      (ceiling : Fraction.Rational) <
        (SquareThreshold.Basic.squareThreshold ceiling : Fraction.Rational) ^ 2 := by
    have castStrict := Fraction.Cast.Order.natCast_lt_direct
      ceilingLtDenominatorSqNat
    rw [NatCast.mul] at castStrict
    simpa only [pow_two] using castStrict
  change coefficient / target < (SquareThreshold.Basic.squareThreshold ceiling : Fraction.Rational) ^ 2
  exact ratioLeCeiling.trans_lt ceilingLtDenominatorSq

/-- Clearing the positive target denominator converts the ratio estimate into the multiplication estimate used below. -/
theorem coefficient_le_target_mul_targetDenominator_sq
    {coefficient target : Fraction.Rational} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient ≤ target *
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 := by
  have ratioStrict := Approximation.Rational.QuadraticTarget.Basic.ratio_lt_targetDenominator_sq coefficientPositive
    targetPositive
  have scaledStrict : coefficient <
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 *
        target :=
    (Fraction.Order.Field.div_lt_iff_pos targetPositive).mp ratioStrict
  calc
    coefficient ≤
        (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 *
          target :=
      scaledStrict.le
    _ = target *
        (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 :=
          by ring1

/-- Exact algebraic form of the reciprocal-square request. -/
theorem coefficient_mul_targetEpsilon_sq_eq_div
    (coefficient target : Fraction.Rational) :
    coefficient * Approximation.Rational.QuadraticTarget.Basic.targetEpsilon coefficient target ^ 2 =
      coefficient /
        (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 :=
          by
  let denominator : Fraction.Rational := Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient
    target
  have oneDiv : (1 : Fraction.Rational) / denominator = denominator⁻¹ := by
    rw [Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Field.one_mul denominator⁻¹
  change coefficient * ((1 : Fraction.Rational) / denominator) ^ 2 =
    coefficient / denominator ^ 2
  rw [oneDiv, Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.inv_pow_direct]

/-- The square-root-scaled request is sufficient for any positive quadratic coefficient and positive residual target. -/
theorem coefficient_mul_targetEpsilon_sq_le
    {coefficient target : Fraction.Rational} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient * Approximation.Rational.QuadraticTarget.Basic.targetEpsilon coefficient target ^ 2 ≤ target := by
  have denominatorPositive : (0 : Fraction.Rational) <
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator_pos coefficient target)
  have squarePositive :
      0 < (Approximation.Rational.QuadraticTarget.Basic.targetDenominator coefficient target : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct denominatorPositive 2
  rw [Approximation.Rational.QuadraticTarget.Basic.coefficient_mul_targetEpsilon_sq_eq_div]
  exact (Fraction.Order.Field.div_le_iff_pos squarePositive).mpr
    (Approximation.Rational.QuadraticTarget.Basic.coefficient_le_target_mul_targetDenominator_sq coefficientPositive
      targetPositive)
end Purelib.Approximation.Rational.QuadraticTarget.Basic

end
