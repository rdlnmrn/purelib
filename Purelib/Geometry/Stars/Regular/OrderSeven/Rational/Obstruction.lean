module
import Purelib.Algebra.Group.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Divisibility
import Purelib.Data.Nat.Multiplication
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Geometry.Stars.Regular.OrderSeven.Basic
import Purelib.Geometry.Stars.Regular.OrderSeven.Classification
import Purelib.NumberTheory.Divisibility.Seven.Cube

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.Geometry.Stars.Regular

open Purelib.Geometry.Stars.Regular.OrderSeven

open Purelib.NumberTheory

section
public section

/-!
# Divine Proportions, Example 14.10

The rational exclusion is the finite Eisenstein-at-seven argument applied to
the computable gcd-reduced numerator and denominator.  The three decimal
displays are retained as exact rational sign-change brackets; no completed
decimal field, real root, or limit object is introduced.
-/

attribute [local instance 2000] Group.Negation.subNegZeroMonoid

namespace Purelib.Geometry.Stars.Regular.OrderSeven.Rational

namespace Obstruction

/-- The rational clause of Example 14.10: the displayed cubic has no constructive-rational root. Its reversed polynomial
is Eisenstein at seven; the proof below spells out that finite numerator/denominator argument. -/
theorem cubic_has_no_rational_root (value : Fraction.Rational) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
  intro cubicZero
  let reduced := Fraction.Basic.representative value
  let numerator := reduced.num
  let denominator := reduced.den
  have clearDenominator :
      value * (denominator : Fraction.Rational) = (numerator : Fraction.Rational) := by
    exact Fraction.Cast.representative_mul_den value
  have clearedRational :
      7 * (denominator : Fraction.Rational) ^ 3 -
          56 * (numerator : Fraction.Rational) * (denominator : Fraction.Rational) ^ 2 +
          112 * (numerator : Fraction.Rational) ^ 2 * (denominator : Fraction.Rational) -
          64 * (numerator : Fraction.Rational) ^ 3 = 0 := by
    calc
      7 * (denominator : Fraction.Rational) ^ 3 -
            56 * (numerator : Fraction.Rational) * (denominator : Fraction.Rational) ^ 2 +
            112 * (numerator : Fraction.Rational) ^ 2 * (denominator : Fraction.Rational) -
            64 * (numerator : Fraction.Rational) ^ 3 =
          (denominator : Fraction.Rational) ^ 3 *
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) := by
        rw [← clearDenominator]
        ring1
      _ = 0 := by rw [cubicZero]; ring1
  have clearedCast :
      ((7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 : Int) : Fraction.Rational) = (0 : Int) := by
    change
      ((7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 : Int) : Fraction.Rational) = (0 : Fraction.Rational)
    simpa only [Ring.IntCast.sub, Ring.IntCast.add, Ring.IntCast.intCast_mul,
      Ring.IntCast.intCast_pow,
      Int.cast_natCast, Int.cast_ofNat, -eq_self, -iff_self] using clearedRational
  have integerEquation :
      7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 = 0 :=
    Fraction.Cast.Compatibility.intCast_injective_direct clearedCast
  have numeratorCubeDivisibleInt : (7 : Int) ∣ numerator ^ 3 := by
    let quotient :=
      (denominator : Int) ^ 3 -
        8 * numerator * (denominator : Int) ^ 2 +
        16 * numerator ^ 2 * (denominator : Int) -
        9 * numerator ^ 3
    refine ⟨quotient, ?_⟩
    calc
      numerator ^ 3 =
          64 * numerator ^ 3 - 63 * numerator ^ 3 := by ring1
      _ = 7 *
          ((denominator : Int) ^ 3 -
            8 * numerator * (denominator : Int) ^ 2 +
            16 * numerator ^ 2 * (denominator : Int)) -
          63 * numerator ^ 3 := by
        have rearranged :
            64 * numerator ^ 3 =
              7 * ((denominator : Int) ^ 3 -
                8 * numerator * (denominator : Int) ^ 2 +
                16 * numerator ^ 2 * (denominator : Int)) := by
          apply Group.eq_of_sub_eq_zero
          calc
            64 * numerator ^ 3 -
                7 * ((denominator : Int) ^ 3 -
                  8 * numerator * (denominator : Int) ^ 2 +
                  16 * numerator ^ 2 * (denominator : Int)) =
              -(7 * (denominator : Int) ^ 3 -
                56 * numerator * (denominator : Int) ^ 2 +
                112 * numerator ^ 2 * (denominator : Int) -
                64 * numerator ^ 3) := by ring1
            _ = 0 := by rw [integerEquation]; ring1
        rw [rearranged]
      _ = 7 * quotient := by
        unfold quotient
        ring1
  have numeratorCubeDivisibleNat :
      7 ∣ numerator.natAbs * numerator.natAbs * numerator.natAbs := by
    rcases numeratorCubeDivisibleInt with ⟨factor, factorization⟩
    refine ⟨factor.natAbs, ?_⟩
    have absolute := congrArg Int.natAbs factorization
    calc
      numerator.natAbs * numerator.natAbs * numerator.natAbs = numerator.natAbs ^ 3 := by
        change _ = ((1 * numerator.natAbs) * numerator.natAbs) * numerator.natAbs
        rewrite [Nat.one_mul]
        rfl
      _ = (numerator ^ 3).natAbs := (Data.Int.Arithmetic.natAbs_pow numerator 3).symm
      _ = (7 * factor).natAbs := absolute
      _ = 7 * factor.natAbs := Data.Int.Arithmetic.natAbs_mul 7 factor
  have numeratorDivisibleNat : 7 ∣ numerator.natAbs :=
    Divisibility.Seven.Cube.seven_dvd_of_seven_dvd_cube numeratorCubeDivisibleNat
  have numeratorDivisibleInt : (7 : Int) ∣ numerator := by
    change ((7 : Nat) : Int) ∣ numerator
    exact Data.Int.Divisibility.of_natAbs numeratorDivisibleNat
  rcases numeratorDivisibleInt with ⟨factor, numeratorFactorization⟩
  have bracketZero :
      (denominator : Int) ^ 3 -
        56 * factor * (denominator : Int) ^ 2 +
        784 * factor ^ 2 * (denominator : Int) -
        3136 * factor ^ 3 = 0 := by
    have sevenTimes :
        7 * ((denominator : Int) ^ 3 -
          56 * factor * (denominator : Int) ^ 2 +
          784 * factor ^ 2 * (denominator : Int) -
          3136 * factor ^ 3) = 0 := by
      calc
        7 * ((denominator : Int) ^ 3 -
            56 * factor * (denominator : Int) ^ 2 +
            784 * factor ^ 2 * (denominator : Int) -
            3136 * factor ^ 3) =
          7 * (denominator : Int) ^ 3 -
            56 * numerator * (denominator : Int) ^ 2 +
            112 * numerator ^ 2 * (denominator : Int) -
            64 * numerator ^ 3 := by
          rw [numeratorFactorization]
          ring1
        _ = 0 := integerEquation
    rcases Data.Int.Arithmetic.eq_zero_of_mul_eq_zero sevenTimes with sevenZero | bracketZero
    · exact False.elim ((by decide : (7 : Int) ≠ 0) sevenZero)
    · exact bracketZero
  have denominatorCubeDivisibleInt :
      (7 : Int) ∣ (denominator : Int) ^ 3 := by
    refine ⟨8 * factor * (denominator : Int) ^ 2 -
        112 * factor ^ 2 * (denominator : Int) + 448 * factor ^ 3, ?_⟩
    calc
      (denominator : Int) ^ 3 =
          56 * factor * (denominator : Int) ^ 2 -
            784 * factor ^ 2 * (denominator : Int) +
            3136 * factor ^ 3 := by
        apply Group.eq_of_sub_eq_zero
        calc
          (denominator : Int) ^ 3 -
              (56 * factor * (denominator : Int) ^ 2 -
                784 * factor ^ 2 * (denominator : Int) +
                3136 * factor ^ 3) =
            (denominator : Int) ^ 3 -
              56 * factor * (denominator : Int) ^ 2 +
              784 * factor ^ 2 * (denominator : Int) -
              3136 * factor ^ 3 := by ring1
          _ = 0 := bracketZero
      _ = 7 * (8 * factor * (denominator : Int) ^ 2 -
          112 * factor ^ 2 * (denominator : Int) + 448 * factor ^ 3) := by
        ring1
  have denominatorCubeDivisibleNat :
      7 ∣ denominator * denominator * denominator := by
    apply Data.Int.Divisibility.to_nat
    change (7 : Int) ∣
      (denominator : Int) * (denominator : Int) * (denominator : Int)
    have expanded : (denominator : Int) ^ 3 =
        (denominator : Int) * (denominator : Int) * (denominator : Int) := by
      change ((1 * (denominator : Int)) * (denominator : Int)) * (denominator : Int) = _
      rewrite [Int.one_mul]
      rfl
    exact (congrArg (fun number : Int => (7 : Int) ∣ number) expanded).mp denominatorCubeDivisibleInt
  have denominatorDivisible : 7 ∣ denominator :=
    Divisibility.Seven.Cube.seven_dvd_of_seven_dvd_cube denominatorCubeDivisibleNat
  rcases reduced.reduced with ⟨reducedCertificate⟩
  have absurd : 7 = 1 := reducedCertificate.eq_one_of_dvd
    numeratorDivisibleNat denominatorDivisible
  omega0

/-- Consequently no regular order-seven star exists over the constructive rationals. -/
theorem no_rational_star : ¬ Nonempty (OrderSeven.Basic.RegularSevenStar Fraction.Rational) := by
  rintro ⟨star⟩
  have parameters := Classification.order_seven_star_parameters
    (K := Fraction.Rational) (by decide) star
  rcases parameters with ⟨value, _valueNonzero, cubicZero, _spreadSquare⟩
  exact Geometry.Stars.Regular.OrderSeven.Rational.Obstruction.cubic_has_no_rational_root value cubicZero
end Obstruction

end Purelib.Geometry.Stars.Regular.OrderSeven.Rational

end
