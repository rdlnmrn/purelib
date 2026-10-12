module
public import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Quadratic.Pair.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Quadratic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 9: finite turn-rational functions

Exercise 9.3 asks for the rational function obtained after a requested finite
number of equal turn-compositions.  The numerator and denominator are the two
coordinates of `(1 + j u)^n` in the executable pair ring with `j²=-1`.
Consequently every index is a finite power and every general coefficient
formula below is an explicitly bounded binomial prefix.
-/

namespace Purelib.Geometry.Trigonometry.Turn.Rational.Basic

/-- The finite pair whose imaginary and real coordinates are respectively the numerator and denominator of the `n`th
turn-rational function. -/
def turnRationalPair
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    Algebra.Quadratic.Pair R 1 :=
  (⟨1, value⟩ : Algebra.Quadratic.Pair R 1) ^ index

/-- Numerator of the `n`th turn-rational function. -/
def turnRationalNumerator
    {R : Type*} [CommRing R] (index : Nat) (value : R) : R :=
  (turnRationalPair index value).im

/-- Denominator of the `n`th turn-rational function. -/
def turnRationalDenominator
    {R : Type*} [CommRing R] (index : Nat) (value : R) : R :=
  (turnRationalPair index value).re

/-- The source's rational function `Uₙ`. Its meaningful quotient statements below expose the corresponding nonzero
denominator. -/
def turnRationalFunction
    {K : Type*} [Algebra.Field.ExplicitField K] (index : Nat) (value : K) : K :=
  turnRationalNumerator index value /
    turnRationalDenominator index value

/-- The zeroth turn-rational numerator is zero. -/
@[simp] theorem turnRationalNumerator_zero
    {R : Type*} [CommRing R] (value : R) :
    turnRationalNumerator 0 value = 0 := rfl

/-- The zeroth turn-rational denominator is one. -/
@[simp] theorem turnRationalDenominator_zero
    {R : Type*} [CommRing R] (value : R) :
    turnRationalDenominator 0 value = 1 := rfl

/-- The numerator update for one additional equal turn. -/
theorem turnRationalNumerator_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    turnRationalNumerator (index + 1) value =
      turnRationalNumerator index value +
        value * turnRationalDenominator index value := by
  unfold turnRationalNumerator
    turnRationalDenominator
    turnRationalPair
  rw [pow_succ]
  simp only [Algebra.Quadratic.Pair.mul_im]
  ring1

/-- The denominator update for one additional equal turn. -/
theorem turnRationalDenominator_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    turnRationalDenominator (index + 1) value =
      turnRationalDenominator index value -
        value * turnRationalNumerator index value := by
  unfold turnRationalNumerator
    turnRationalDenominator
    turnRationalPair
  rw [pow_succ]
  simp only [Algebra.Quadratic.Pair.mul_re]
  ring1
end Purelib.Geometry.Trigonometry.Turn.Rational.Basic

end
