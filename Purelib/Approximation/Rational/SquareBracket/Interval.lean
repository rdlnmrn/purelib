module

import Purelib.Data.Rat.Fraction.Constants
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.SquareBracket.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.SquareBracket

open Purelib.Approximation.Rational.SquareBracket.Basic

open Purelib.Data.Rat

public section

/-!
# Finite dyadic square brackets

A bounded natural recursion selects a positive dyadic rational whose square
lies immediately above a displayed target in `(0, 1)`.  It then performs a
coefficient-computed finite number of rational bisections.  Given any
displayed rational factor greater than one, the returned square lies above
the target and at most that factor times it.  No square root or limiting
object is used.
-/

/-! ## Accuracy-parameterized finite tightening -/

namespace Purelib.Approximation.Rational.SquareBracket.Interval

set_option genInjectivity false in
/-- A positive rational interval bracketing the positive square root of a displayed target.

The two retained endpoints are ordered and carry both square comparisons.
The record contains finite rational data and checked inequalities only. -/
structure SquareInterval (target : Fraction.Rational) where
  /-- The retained lower rational endpoint. -/ lower : Fraction.Rational
  /-- The retained upper rational endpoint. -/ upper : Fraction.Rational
  /-- The lower endpoint is strictly positive. -/ lowerPositive : 0 < lower
  /-- The upper endpoint is strictly positive. -/ upperPositive : 0 < upper
  /-- The endpoints are ordered. -/ lower_le_upper : lower ≤ upper
  /-- The lower endpoint squared does not exceed the target. -/ lowerSq_le_target : lower ^ 2 ≤ target
  /-- The target lies strictly below the upper endpoint squared. -/ target_lt_upperSq : target < upper ^ 2

constructive_injectivity SquareInterval

end Purelib.Approximation.Rational.SquareBracket.Interval

namespace Purelib.Approximation.Rational.SquareBracket.Basic.Bracket

/-- The factor-four bracket supplies the initial square interval `[radius / 2, radius]`.

The original positive radius is retained as the upper endpoint. Its factor-four
square bound certifies the lower endpoint obtained by exact rational halving. -/
@[expose] def toSquareInterval {target : Fraction.Rational}
    (bracket : SquareBracket.Basic.Bracket target) : Interval.SquareInterval target := by
  let lower := (1 / 2 : Fraction.Rational) * bracket.radius
  have lowerPositive : 0 < lower :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      bracket.radiusPositive
  have lowerLeUpper : lower ≤ bracket.radius := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Fraction.Rational) ≤ 1 by decide)
        bracket.radiusPositive.le
    simpa only [lower, _root_.one_mul] using scaled
  have quarterNonnegative : (0 : Fraction.Rational) ≤ 1 / 4 := by decide
  have lowerSqLe : lower ^ 2 ≤ target := by
    have halfSquare : (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 := by decide
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        bracket.square_le_four_target quarterNonnegative
    calc
      lower ^ 2 = (1 / 2 : Fraction.Rational) ^ 2 * bracket.radius ^ 2 := by
        dsimp only [lower]
        ring1
      _ = (1 / 4 : Fraction.Rational) * bracket.radius ^ 2 := by rw [halfSquare]
      _ ≤ (1 / 4 : Fraction.Rational) * (4 * target) := scaled
      _ = target := by
        have quarterFour : (1 / 4 : Fraction.Rational) * 4 = 1 := by decide
        rw [← Fraction.Field.mul_assoc, quarterFour,
          _root_.one_mul]
  exact
    { lower := lower
      upper := bracket.radius
      lowerPositive := lowerPositive
      upperPositive := bracket.radiusPositive
      lower_le_upper := lowerLeUpper
      lowerSq_le_target := lowerSqLe
      target_lt_upperSq := bracket.target_lt_square }

end Purelib.Approximation.Rational.SquareBracket.Basic.Bracket

namespace Purelib.Approximation.Rational.SquareBracket.Interval.SquareInterval

/-- Rational midpoint of a displayed square interval. -/
@[expose] def midpoint {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : Fraction.Rational :=
  Fraction.Arithmetic.normalizedMul (1 / 2 : Fraction.Rational)
    (Fraction.Arithmetic.normalizedAdd interval.lower interval.upper)

/-- The normalized midpoint of a square interval is strictly positive. -/
theorem midpoint_pos {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : 0 < interval.midpoint :=
  (by
    simp only [Interval.SquareInterval.midpoint,
      Fraction.Arithmetic.normalizedMul_eq,
      Fraction.Arithmetic.normalizedAdd_eq]
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_direct
        interval.lowerPositive interval.upperPositive))

/-- The midpoint is at least the lower endpoint. -/
theorem lower_le_midpoint {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : interval.lower ≤ interval.midpoint := by
    have doubled := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl interval.lower)
      interval.lower_le_upper
    have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      interval.lower = (1 / 2 : Fraction.Rational) *
          (interval.lower + interval.lower) :=
        (Purelib.Data.Rat.Fraction.Constants.half_double interval.lower).symm
      _ ≤ (1 / 2 : Fraction.Rational) *
          (interval.lower + interval.upper) :=
        scaled
      _ = interval.midpoint := by
        symm
        simp only [Interval.SquareInterval.midpoint,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedAdd_eq, -eq_self, -iff_self]
        rfl

/-- The midpoint is at most the upper endpoint. -/
theorem midpoint_le_upper {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : interval.midpoint ≤ interval.upper := by
    have doubled := Fraction.Order.Arithmetic.add_le_add_direct interval.lower_le_upper
      (Fraction.Order.Basic.le_refl interval.upper)
    have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      interval.midpoint = (1 / 2 : Fraction.Rational) *
          (interval.lower + interval.upper) := by
        simp only [Interval.SquareInterval.midpoint,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedAdd_eq, -eq_self, -iff_self]
        rfl
      _ ≤ (1 / 2 : Fraction.Rational) *
          (interval.upper + interval.upper) :=
        scaled
      _ = interval.upper := Purelib.Data.Rat.Fraction.Constants.half_double interval.upper

/-- One exact rational comparison retains the half which still brackets the target.

The target-to-midpoint square comparison selects the original lower endpoint
or the original upper endpoint together with the midpoint and its certificates. -/
@[expose] def bisect {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : Interval.SquareInterval target :=
  if midpointAbove : target < interval.midpoint ^ 2 then
    { lower := interval.lower
      upper := interval.midpoint
      lowerPositive := interval.lowerPositive
      upperPositive := interval.midpoint_pos
      lower_le_upper := interval.lower_le_midpoint
      lowerSq_le_target := interval.lowerSq_le_target
      target_lt_upperSq := midpointAbove }
  else
    { lower := interval.midpoint
      upper := interval.upper
      lowerPositive := interval.midpoint_pos
      upperPositive := interval.upperPositive
      lower_le_upper := interval.midpoint_le_upper
      lowerSq_le_target := le_of_not_gt midpointAbove
      target_lt_upperSq := interval.target_lt_upperSq }

end Purelib.Approximation.Rational.SquareBracket.Interval.SquareInterval

end
