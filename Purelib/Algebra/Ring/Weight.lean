module

public import Purelib.Algebra.Ring.Basic
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Rational squared weights of finite ring data

The displayed rational weight need not separate points or assign one to the
unit. Its finite sum and product bounds retain a single explicit multiplier,
allowing the original scalar payload to remain unchanged.
-/

public section

namespace Purelib.Algebra.Ring

open Purelib.Data.Rat.Fraction (Rational)

set_option genInjectivity false in
/-- A nonnegative rational weight with squared triangle and bounded product laws.

The retained multiplier is at least one. No topology, division, positive
definiteness or norm of the unit is required.
-/
structure Weight (K : Type*) [CommRing K] where
  /-- The executable rational weight of the original scalar payload. -/ value : K → Rational
  /-- Every original scalar has nonnegative weight. -/ nonnegative : ∀ scalar, 0 ≤ value scalar
  /-- The original zero has zero weight. -/ zero : value 0 = 0
  /-- Negating an original scalar preserves its weight. -/ neg : ∀ scalar, value (-scalar) = value scalar
  /-- The original addition has the squared triangle bound. -/
  add_le : ∀ left right, value (left + right) ≤ 2 * (value left + value right)
  /-- The retained uniform multiplier for original products. -/ multiplier : Rational
  /-- The product multiplier is at least one. -/ one_le_multiplier : 1 ≤ multiplier
  /-- The original product obeys the retained uniform bound. -/
  mul_le : ∀ left right, value (left * right) ≤ multiplier * value left * value right

constructive_injectivity Weight

namespace Weight

open Purelib.Data.Rat.Fraction
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order

variable {K : Type*} [CommRing K]

/-- The retained uniform product multiplier is nonnegative. -/
theorem multiplier_nonnegative (weight : Weight K) : 0 ≤ weight.multiplier :=
  (by decide : (0 : Rational) ≤ 1).trans weight.one_le_multiplier

/-- The original finite sum has weight bounded by its finite table of individual weights.

The factor is the rational power of two at the same explicit table length;
the empty table and zero weights require no separate positivity assumption.
-/
theorem sum_le (weight : Weight K) {count : Nat} (values : Fin count → K) :
    weight.value (sumFin values) ≤ (2 : Rational) ^ count * sumFin (fun index => weight.value (values index)) := by
  induction count with
  | zero =>
      change weight.value 0 ≤ (2 : Rational) ^ 0 * 0
      rewrite [weight.zero, mul_zero]
      exact le_rfl
  | succ count previous =>
      rewrite [sumFin_succ, sumFin_succ]
      have oneLe : (1 : Rational) ≤ 2 ^ count := by
        have bound := Order.Arithmetic.pow_le_pow_direct
          (by decide : (0 : Rational) ≤ 1) (by decide : (1 : Rational) ≤ 2) count
        rewrite [one_pow] at bound
        exact bound
      have first := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe (weight.nonnegative (values 0))
      rewrite [one_mul] at first
      calc
        weight.value (values 0 + sumFin (fun index => values index.succ)) ≤
            2 * (weight.value (values 0) + weight.value (sumFin (fun index => values index.succ))) :=
          weight.add_le _ _
        _ ≤ 2 * (2 ^ count * weight.value (values 0) +
            2 ^ count * sumFin (fun index => weight.value (values index.succ))) :=
          Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Order.Arithmetic.add_le_add_direct first (previous (fun index => values index.succ))) (by decide)
        _ = 2 ^ (count + 1) *
            (weight.value (values 0) + sumFin (fun index => weight.value (values index.succ))) := by
          rewrite [pow_succ]
          ring0

end Weight

end Purelib.Algebra.Ring

end
