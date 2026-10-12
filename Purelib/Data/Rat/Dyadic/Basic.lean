module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite dyadic normalization of a positive constructive fraction

For one displayed positive rational, a bounded binary scan finds a dyadic
scaling into the deliberately interior interval `[3/4,3/2]`.  The scan fuel
is the computed rational ceiling (or the ceiling of the reciprocal), so this
module contains no unbounded search or Archimedean existence principle.
-/

namespace Purelib.Data.Rat.Dyadic.Basic

open Purelib.Data.Rat

/-- Choose whether a dyadic normalization divides or multiplies by a power of two. -/
inductive Direction where
  /-- Divide the original rational by the selected power of two. -/ | down
  /-- Multiply the original rational by the selected power of two. -/ | up
deriving DecidableEq

derive_exposed_repr Purelib.Data.Rat.Dyadic.Basic.Direction

/-- Compute two raised to the supplied natural exponent in the canonical rational carrier. -/
def power (exponent : Nat) : Fraction.Rational := (2 : Fraction.Rational) ^
  exponent

/-- Compute the positive dyadic multiplier selected by a direction and natural exponent. -/
def factor : Dyadic.Basic.Direction → Nat → Fraction.Rational
  | .down, exponent => 1 / Dyadic.Basic.power exponent
  | .up, exponent => Dyadic.Basic.power exponent

/-- Scale a rational down by division or up by multiplication by the selected power of two. -/
def normalized (value : Fraction.Rational) : Dyadic.Basic.Direction → Nat →
  Fraction.Rational
  | .down, exponent => value / Dyadic.Basic.power exponent
  | .up, exponent => Dyadic.Basic.power exponent * value

/-- Every natural power of the rational number two is positive. -/
theorem power_pos (exponent : Nat) : 0 <
  Dyadic.Basic.power exponent :=
  Fraction.Order.Arithmetic.pow_pos_direct (by decide) exponent

/-- Every selected dyadic scaling factor is positive. -/
theorem factor_pos (direction : Dyadic.Basic.Direction) (exponent : Nat) :
    0 < Dyadic.Basic.factor direction exponent := by
  cases direction with
  | down =>
      exact Fraction.Order.Field.div_pos_direct (by decide)
        (Dyadic.Basic.power_pos exponent)
  | up => exact Dyadic.Basic.power_pos exponent

/-- Directional normalization equals multiplication by the corresponding dyadic factor. -/
theorem normalized_eq_factor_mul (value : Fraction.Rational)
    (direction : Dyadic.Basic.Direction) (exponent : Nat) :
    Dyadic.Basic.normalized value direction exponent = Dyadic.Basic.factor direction exponent * value := by
  cases direction with
  | down =>
      change value * (Dyadic.Basic.power exponent)⁻¹ =
        (1 * (Dyadic.Basic.power exponent)⁻¹) * value
      rw [Fraction.Field.one_mul,
        Fraction.Field.mul_comm]
  | up => rfl

/-- Increasing the dyadic exponent by one multiplies its rational power by two. -/
theorem power_succ (exponent : Nat) :
    Dyadic.Basic.power (exponent + 1) = Dyadic.Basic.power exponent * 2 := by
  rw [Dyadic.Basic.power, Dyadic.Basic.power, pow_succ]

/-- Scaling down at one exponent gives twice the value at the successor exponent. -/
theorem down_previous_eq_two_down (value :
  Fraction.Rational)
    (exponent : Nat) :
    Dyadic.Basic.normalized value .down exponent =
      2 * Dyadic.Basic.normalized value .down (exponent + 1) := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (Dyadic.Basic.power_pos exponent).ne'
  calc
    Dyadic.Basic.normalized value .down exponent * Dyadic.Basic.power exponent = value :=
      Fraction.Field.div_mul_cancel_of_ne value _
        (Dyadic.Basic.power_pos exponent).ne'
    _ = Dyadic.Basic.normalized value .down (exponent + 1) * Dyadic.Basic.power (exponent + 1) :=
      (Fraction.Field.div_mul_cancel_of_ne value _
        (Dyadic.Basic.power_pos (exponent + 1)).ne').symm
    _ = (2 * Dyadic.Basic.normalized value .down (exponent + 1)) *
        Dyadic.Basic.power exponent := by
      rw [Dyadic.Basic.power_succ]
      ring1

/-- Scaling up at the successor exponent gives twice the previous scaled value. -/
theorem up_succ_eq_two_up (value :
  Fraction.Rational) (exponent : Nat) :
    Dyadic.Basic.normalized value .up (exponent + 1) =
      2 * Dyadic.Basic.normalized value .up exponent := by
  rw [Dyadic.Basic.normalized, Dyadic.Basic.normalized, Dyadic.Basic.power_succ]
  ring1

end Purelib.Data.Rat.Dyadic.Basic

end

section
@[expose] public section

/-!
# Finite dyadic range reduction for the progressive logarithm

A logarithm needs branch information.  This module records that information
as one finite dyadic chart: a natural exponent, a scaling direction, and a
proof that every candidate at the displayed input state is carried into the
overlapping real interval `[1/2,2]`.

The output is the local finite logarithm of the scaled input plus or minus an
explicit natural multiple of the independently generated finite `log 2`
samples.  No completed logarithm, limiting value, or infinite functional
equation appears in the construction.
-/

namespace Purelib.Data.Rat.Dyadic.Basic

open Purelib.Data.Rat

/-- Read the canonical rational power of two at the supplied exponent. -/
def dyadicPower (exponent : Nat) : Fraction.Rational :=
  Dyadic.Basic.power exponent

/-- Read the directional dyadic scalar for the supplied exponent. -/
def dyadicScalar (direction : Dyadic.Basic.Direction) (exponent : Nat) :
  Fraction.Rational :=
  Dyadic.Basic.factor direction exponent
end Purelib.Data.Rat.Dyadic.Basic

end
