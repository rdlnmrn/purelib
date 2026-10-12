module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Contraction
public import Purelib.Approximation.Rational.SquareBracket.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction (Rational)

open Purelib

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite dyadic square brackets

A bounded natural recursion selects a positive dyadic rational whose square
lies immediately above a displayed target in `(0, 1)`.  It then performs a
coefficient-computed finite number of rational bisections.  Given any
displayed rational factor greater than one, the returned square lies above
the target and at most that factor times it.  No square root or limiting
object is used.
-/

namespace Purelib.Approximation.Rational.SquareBracket.Dyadic

/-- Find a factor-four square bracket by a bounded sequence of radius halvings.

The supplied radius is positive and initially above the target in square; a terminal square bound ensures that the
recursion finds the first crossing before its finite fuel is exhausted. -/
def search (target radius :
  Rational) :
    (fuel : Nat) ->
      0 < radius ->
      target < radius ^ 2 ->
      ((1 / 2 : Rational) ^ fuel * radius) ^ 2 <= target ->
      Purelib.Approximation.Rational.SquareBracket.Basic.Bracket target
  | 0, radiusPositive, above, terminal => by
      have below : radius ^ 2 <= target := by
        simpa only [pow_zero, one_mul] using terminal
      exact ((not_lt_of_ge below) above).elim
  | fuel + 1, radiusPositive, above, terminal => by
      let next := (1 / 2 : Rational) * radius
      have nextPositive : 0 < next :=
        Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) radiusPositive
      if nextAbove : target < next ^ 2 then
        have nextTerminal :
            ((1 / 2 : Rational) ^ fuel * next) ^ 2 <= target := by
          calc
            ((1 / 2 : Rational) ^ fuel * next) ^ 2 =
                ((1 / 2 : Rational) ^ (fuel + 1) * radius) ^ 2 := by
              dsimp only [next]
              rw [pow_succ]
              ring1
            _ <= target := terminal
        exact search target next fuel nextPositive nextAbove
          nextTerminal
      else
        have nextBelow : next ^ 2 <= target := le_of_not_gt nextAbove
        have scaled : 4 * next ^ 2 <= 4 * target :=
          Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            nextBelow (by decide)
        exact
          { radius := radius
            radiusPositive := radiusPositive
            target_lt_square := above
            square_le_four_target := by
              have coefficient :
                  (4 : Rational) * (1 / 2 : Rational) ^ 2 = 1 := by
                decide
              calc
                radius ^ 2 = 4 * next ^ 2 := by
                  dsimp only [next]
                  have squareProduct :
                      ((1 / 2 : Fraction.Rational) * radius) ^ 2 =
                        (1 / 2 : Fraction.Rational) ^ 2 * radius ^ 2 := by
                    rw [pow_two, pow_two, pow_two]
                    ring1
                  rw [squareProduct]
                  calc
                    radius ^ 2 = 1 * radius ^ 2 := by ring1
                    _ = (4 * (1 / 2 : Rational) ^ 2) * radius ^ 2 := by
                      rw [coefficient]
                    _ = 4 * ((1 / 2 : Rational) ^ 2 * radius ^ 2) := by
                      ring1
                _ <= 4 * target := scaled }

/-- Coefficient-computed recursion fuel. The existing geometric-depth bound makes a dyadic power small enough before the
recursion can run out. -/
def bracketFuel (target : Fraction.Rational) : Nat :=
  Contraction.geometricDepth 1 target

/-- Select the first dyadic square above a displayed target in `(0, 1)`. The construction performs only the bounded
recursion `bracketFuel target`; it does not compute or postulate a square root. -/
def select (target : Fraction.Rational) (targetPositive : 0 <
  target)
    (target_lt_one : target < 1) : SquareBracket.Basic.Bracket target := by
  let fuel := bracketFuel target
  let halfPower := (1 / 2 : Fraction.Rational) ^ fuel
  have geometric : (2 / 3 : Fraction.Rational) ^ fuel <= target := by
    have bound :=
      Contraction.geometricDepth_sufficient
        (width := (1 : Fraction.Rational)) (epsilon := target)
        (by decide) targetPositive
    simpa only [fuel, bracketFuel, mul_one] using bound
  have halfPowerLeGeometric : halfPower <= (2 / 3 : Fraction.Rational) ^ fuel := by
    exact Fraction.Order.Arithmetic.pow_le_pow_direct
      (show (0 : Fraction.Rational) <= 1 / 2 by decide)
      (show (1 / 2 : Fraction.Rational) <= 2 / 3 by decide) fuel
  have halfPowerLeTarget : halfPower <= target :=
    halfPowerLeGeometric.trans geometric
  have halfPowerNonnegative : 0 <= halfPower :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) fuel
  have halfPowerLeOne : halfPower <= 1 := by
    simpa only [halfPower, one_pow] using
      (Fraction.Order.Arithmetic.pow_le_pow_direct
        (show (0 : Fraction.Rational) <= 1 / 2 by decide)
        (show (1 / 2 : Fraction.Rational) <= 1 by decide) fuel)
  have terminal : (halfPower * 1) ^ 2 <= target := by
    have squareLe : halfPower ^ 2 <= halfPower := by
      rw [pow_two]
      simpa only [one_mul] using
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          halfPowerLeOne halfPowerNonnegative
    simpa only [mul_one] using squareLe.trans halfPowerLeTarget
  exact search target 1 fuel (by decide) (by
      simpa only [one_pow]
        using target_lt_one) (by simpa only [halfPower] using terminal)
end Purelib.Approximation.Rational.SquareBracket.Dyadic

end
