module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Geometric.Quarter

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Quarter powers and finite rational geometric allowances

The original rational powers, finite sums and scaled allowances retain their
exact arithmetic data. Their certificates concern supplied finite indices
and nonnegative or positive scales, without an infinite completion.
-/

namespace Purelib.Approximation.Rational.Geometric.Basic

open Purelib
open Purelib.Algebra
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Geometric

/-- A rational squared-error allowance with quarter-power decay.

The supplied scale is divided by the original power of four at the
finite index. The returned rational is that same displayed squared-error allowance. -/
@[expose] public def quarterRadius (scale : Fraction.Rational) (index : Nat) : Fraction.Rational :=
  scale / (4 : Fraction.Rational) ^ index

/-- Express the quarter-radius as its scale times a quarter-power.

The inverse-power law identifies the original division by a power of
four with multiplication by the corresponding rational quarter power. -/
public theorem quarterRadius_eq_mul_pow (scale : Fraction.Rational) (index : Nat) :
    quarterRadius scale index = scale * (1 / 4 : Fraction.Rational) ^ index := by
  rw [quarterRadius, Algebra.Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.inv_pow_direct,
    Algebra.Field.ExplicitField.div_eq_mul_inv,
    _root_.one_mul]

/-- A nonnegative scale gives a nonnegative quarter-radius at every stage.

The retained scale is nonnegative, and every original denominator power
is positive. Their quotient retains the supplied scale's nonnegative sign. -/
public theorem quarterRadius_nonneg {scale : Fraction.Rational} (nonnegative : 0 ≤ scale)
    (index : Nat) :
    0 ≤ quarterRadius scale index := by
  exact Order.Field.div_nonneg_direct nonnegative
    (Order.Arithmetic.pow_nonneg_direct (by decide) index)

/-- A positive scale gives a positive quarter-radius at every stage.

The retained scale and every original denominator power are positive.
Their quotient is therefore positive at every finite index. -/
public theorem quarterRadius_pos {scale : Fraction.Rational} (positive : 0 < scale)
    (index : Nat) :
    0 < quarterRadius scale index := by
  exact Order.Field.div_pos_direct positive
    (Order.Arithmetic.pow_pos_direct (by decide) index)

/-- Every quarter-radius is at most its nonnegative initial scale.

Every nonnegative quarter power is at most one. Multiplication by the
supplied nonnegative scale bounds the original allowance by that same scale. -/
public theorem quarterRadius_le_scale {scale : Fraction.Rational} (nonnegative : 0 ≤ scale)
    (index : Nat) :
    quarterRadius scale index ≤ scale := by
  rw [quarterRadius_eq_mul_pow]
  have powerBound : (1 / 4 : Fraction.Rational) ^ index ≤ 1 := by
    have bound := Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1 / 4)
      (by decide : (1 / 4 : Fraction.Rational) ≤ 1) index
    simpa only [one_pow] using bound
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    powerBound nonnegative
  simpa only [Fraction.Field.mul_one_direct] using scaled

/-- Quarter-radii at a nonnegative scale decrease as the finite stage increases.

The supplied stage order bounds the original later quarter power by
the earlier one. The retained nonnegative scale transports that same
finite scalar bound to the original displayed allowances. -/
public theorem quarterRadius_antitone {scale : Fraction.Rational}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    quarterRadius scale later ≤ quarterRadius scale earlier := by
  rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Quarter.quarterPower_antitone order) scaleNonnegative

/-- Quarter-radii are monotone in their scale at a fixed stage.

The two retained scales are ordered at the same finite index.
Multiplication by that original nonnegative quarter power preserves
the supplied order without altering either scale or allowance. -/
public theorem quarterRadius_scale_mono {small large : Fraction.Rational}
    (scaleOrder : small ≤ large) (index : Nat) :
    quarterRadius small index ≤
      quarterRadius large index := by
  rw [quarterRadius_eq_mul_pow,
    quarterRadius_eq_mul_pow]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaleOrder
    (Order.Arithmetic.pow_nonneg_direct (by decide) _)

/-- Combine three quarter-radii at one stage using the displayed weights two, four and four.

All three original allowances use the same finite quarter power.
Distributing their displayed rational weights retains the exact
combined scale two times the sum with weights one, two and two. -/
public theorem quarterRadius_weighted_sum
    (left middle right : Fraction.Rational) (index : Nat) :
    2 * (quarterRadius left index +
      2 * (quarterRadius middle index +
        quarterRadius right index)) =
      quarterRadius
        (2 * (left + 2 * (middle + right))) index := by
  simp only [quarterRadius_eq_mul_pow]
  ring1

end Purelib.Approximation.Rational.Geometric.Basic
