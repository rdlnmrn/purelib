module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Nat.Search.First
public import Purelib.Data.Rat.Dyadic.Basic
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Rounding.Floor

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Purelib.Algebra.NatCast

section
public section

/-!
# Finite dyadic normalization of a positive constructive fraction

For one displayed positive rational, a bounded binary scan finds a dyadic
scaling into the deliberately interior interval `[3/4,3/2]`.  The scan fuel
is the computed rational ceiling (or the ceiling of the reciprocal), so this
module contains no unbounded search or Archimedean existence principle.
-/

namespace Purelib.Data.Rat.Dyadic.PowerCeiling

open Purelib.Data.Rat

open Purelib.Algebra

/-- Require the given rational to lie below the selected natural power of two. -/
private def powerPredicate (value : Fraction.Rational) (exponent : Nat) : Prop :=
  value ≤ Dyadic.Basic.power exponent

/-- Decide the power-ceiling predicate using the original canonical rational comparison. -/
private instance (value : Fraction.Rational) (exponent : Nat) :
    Decidable (Dyadic.PowerCeiling.powerPredicate value exponent) := by
  unfold Dyadic.PowerCeiling.powerPredicate
  infer_instance

open Purelib.Data.Nat in
/-- Find the first natural power of two at least the supplied positive rational.

Use the natural ceiling of the positive rational as explicit search fuel. Its power of two bounds the value, so the
finite scan returns an exponent, a successful comparison and failure evidence for every earlier exponent. -/
@[expose] def powerCeiling (value : Fraction.Rational) (positive : 0 < value) :
    Search.First.FirstResult
      (fun exponent => value ≤ Dyadic.Basic.power exponent) 0 := by
  let fuel := Rounding.Floor.ceilNat value
  have valueLeFuel : value ≤ (fuel : Fraction.Rational) :=
    Rounding.Floor.le_natCast_ceilNat_of_nonneg positive.le
  have fuelLePowerNat : fuel ≤ 2 ^ fuel :=
    (Nat.le_succ fuel).trans
      (BinaryNormalization.succ_le_two_pow fuel)
  have fuelLePower : (fuel : Fraction.Rational) ≤ Dyadic.Basic.power fuel := by
    have cast := Fraction.Cast.Order.natCast_le_direct fuelLePowerNat
    simpa only [Dyadic.Basic.power, Purelib.Algebra.NatCast.pow, Nat.cast_ofNat] using cast
  apply Search.First.scanFirst
    (fun exponent => value ≤ Dyadic.Basic.power exponent) (fun _ => inferInstance) 0 fuel
  simpa only [Nat.zero_add] using valueLeFuel.trans fuelLePower

/-- The computed first power ceiling bounds the original positive rational from above. -/
theorem powerCeiling_upper (value : Fraction.Rational) (positive : 0 < value) :
    value ≤ Dyadic.Basic.power (Dyadic.PowerCeiling.powerCeiling value positive).exponent :=
  (Dyadic.PowerCeiling.powerCeiling value positive).holds

/-- When the computed ceiling exponent is a successor, the previous power is strictly below the original rational. -/
theorem powerCeiling_previous_lt (value : Fraction.Rational) (positive : 0 < value)
    (previous : Nat)
    (exponentEq : (Dyadic.PowerCeiling.powerCeiling value positive).exponent = previous + 1) :
    Dyadic.Basic.power previous < value := by
  have failure := (Dyadic.PowerCeiling.powerCeiling value positive).before_fails previous
    (Nat.zero_le previous) (by
      calc
        previous < previous + 1 := Nat.lt_succ_self previous
        _ = (Dyadic.PowerCeiling.powerCeiling value positive).exponent := exponentEq.symm)
  exact lt_of_not_ge (by
    exact failure)
end Purelib.Data.Rat.Dyadic.PowerCeiling

end
