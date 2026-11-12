module

import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Rounding.Floor.Bounds
import Purelib.Data.Rat.Fraction.Cast
meta import Purelib.Data.Rat.Rounding.Floor
meta import Purelib.Data.Rat.Fraction.Cast

/-! # Direct denominator readback in rational floor and ceiling -/

namespace TestPurelib.Data.Rat.Rounding.Floor

open Purelib.Data.Rat

example (source : Fraction.Rational) :
    Rounding.Floor.floor source = source.num / (source.den : Int) := Rounding.Floor.floor_eq source

/-- The finite reciprocal ceiling selects eleven cells for a tenth-unit width. -/
example : Rounding.Floor.ceilNat (1 / (1 / 10 : Fraction.Rational)) + 1 = 11 := by decide +kernel

/-- The computed reciprocal count is strictly finer than the original positive width. -/
example : 1 / ((Rounding.Floor.ceilNat (1 / (1 / 10 : Fraction.Rational)) + 1 : Nat) : Fraction.Rational) < 1 / 10 :=
  Rounding.Floor.Bounds.reciprocal_ceilNat_lt _ (by decide)

/-- Execute signed floor and ceiling with a denominator too large for a recursive unary cast. -/
private def checkLargeDenominator : IO Unit := do
  let denominator := Int.ofNat (2 ^ 20 + 17)
  let fraction := Fraction.Cast.fromInt 7 / Fraction.Cast.fromInt denominator
  unless Rounding.Floor.floor fraction = 0 ∧ Rounding.Floor.ceil fraction = 1 ∧
      Rounding.Floor.floor (-fraction) = -1 ∧ Rounding.Floor.ceil (-fraction) = 0 do
    throw (IO.userError "direct denominator conversion changed a signed Euclidean floor or ceiling")
  let shifted := Fraction.Cast.fromInt (-3) + fraction
  unless Rounding.Floor.floor shifted = -3 ∧ Rounding.Floor.ceil shifted = -2 do
    throw (IO.userError "large-denominator floor lost the original signed integer translation")

#eval checkLargeDenominator

end TestPurelib.Data.Rat.Rounding.Floor
