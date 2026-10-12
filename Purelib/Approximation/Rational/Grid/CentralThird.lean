module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

namespace Purelib.Approximation.Rational.Grid.CentralThird

/-! ## Central-third safe cuts -/

/-- Compute the lower central-third point using normalized rational arithmetic.

For endpoints `a` and `b`, this is `a + (b - a) / 3`. -/
def centralLower (a b : Fraction.Rational) : Fraction.Rational
  :=
  Fraction.Arithmetic.normalizedAdd a
    (Fraction.Arithmetic.normalizedDiv
      (Fraction.Arithmetic.normalizedSub b a) 3)

/-- Compute the upper central-third point using normalized rational arithmetic.

For endpoints `a` and `b`, this is `a + 2 * (b - a) / 3`. -/
def centralUpper (a b : Fraction.Rational) : Fraction.Rational
  :=
  Fraction.Arithmetic.normalizedAdd a
    (Fraction.Arithmetic.normalizedMul 2
      (Fraction.Arithmetic.normalizedDiv
        (Fraction.Arithmetic.normalizedSub b a) 3))

/-- Strictly ordered endpoints contain both central-third points in increasing order. -/
theorem centralBounds {a b : Fraction.Rational} (less : a < b) :
    a < centralLower a b ∧
      centralLower a b < centralUpper
        a b ∧
      centralUpper a b < b := by
  have thirdPositive : 0 < (b - a) / 3 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct less) (by decide)
  have thirdScaled : (3 : Fraction.Rational) * ((b - a) / 3) = b - a := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne
      (b - a) 3 (by decide)
  constructor
  · simp only [centralLower, Fraction.Arithmetic.normalizedAdd_eq,
      Fraction.Arithmetic.normalizedDiv_eq,
      Fraction.Arithmetic.normalizedSub_eq]
    calc
      a = a + 0 := by ring1
      _ < a + (b - a) / 3 :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct thirdPositive a
  constructor
  · have shifted :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct thirdPositive
        (centralLower a b)
    calc
      centralLower a b = centralLower
        a b + 0 := by ring1
      _ < centralLower a b + (b - a) / 3 := shifted
      _ = centralUpper a b := by
        simp only [centralLower,
          centralUpper,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        ring1
  · have shifted :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct thirdPositive
        (centralUpper a b)
    calc
      centralUpper a b = centralUpper
        a b + 0 := by ring1
      _ < centralUpper a b + (b - a) / 3 := shifted
      _ = b := by
        simp only [centralUpper,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        calc
          a + 2 * ((b - a) / 3) + (b - a) / 3 =
              a + 3 * ((b - a) / 3) := by ring1
          _ = a + (b - a) := by rw [thirdScaled]
          _ = b := by ring1

/-- Subtracting the base point from its twice-shifted value leaves twice the shift. -/
theorem add_twice_sub_left (a t : Fraction.Rational) :
    a + 2 * t - a = 2 * t := by ring1

/-- When three shifts span the endpoints, the upper endpoint is two shifts above the first interior point. -/
theorem sub_add_eq_twice_of_three_mul
    (a b t : Fraction.Rational) (scaled : 3 * t = b - a) :
    b - (a + t) = 2 * t := by
  calc
    b - (a + t) = (b - a) - t := by ring1
    _ = 3 * t - t := by rw [← scaled]
    _ = 2 * t := by ring1
end Purelib.Approximation.Rational.Grid.CentralThird

end
