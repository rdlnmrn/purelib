module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Geometry.Trigonometry.Turn.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Geometry.Trigonometry.Turn

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

namespace Purelib.Geometry.Trigonometry.Turn.Rational.Values

/-- The numerator and denominator pairs through the fifth requested index. -/
theorem turnRationalPair_first_five
    {R : Type*} [CommRing R] (value : R) :
    (Rational.Basic.turnRationalNumerator 1 value = value ∧
      Rational.Basic.turnRationalDenominator 1 value = 1) ∧
    (Rational.Basic.turnRationalNumerator 2 value = 2 * value ∧
      Rational.Basic.turnRationalDenominator 2 value = 1 - value ^ 2) ∧
    (Rational.Basic.turnRationalNumerator 3 value = 3 * value - value ^ 3 ∧
      Rational.Basic.turnRationalDenominator 3 value = 1 - 3 * value ^ 2) ∧
    (Rational.Basic.turnRationalNumerator 4 value = 4 * value - 4 * value ^ 3 ∧
      Rational.Basic.turnRationalDenominator 4 value =
        1 - 6 * value ^ 2 + value ^ 4) ∧
    (Rational.Basic.turnRationalNumerator 5 value =
        5 * value - 10 * value ^ 3 + value ^ 5 ∧
      Rational.Basic.turnRationalDenominator 5 value =
        1 - 10 * value ^ 2 + 5 * value ^ 4) := by
  simp only [Rational.Basic.turnRationalNumerator, Rational.Basic.turnRationalDenominator,
    Rational.Basic.turnRationalPair, pow_succ, pow_zero,
    Algebra.Quadratic.Pair.one_re, Algebra.Quadratic.Pair.one_im,
    Algebra.Quadratic.Pair.mul_re, Algebra.Quadratic.Pair.mul_im, -eq_self, -iff_self]
  constructor
  · constructor <;> ring1
  constructor
  · constructor <;> ring1
  constructor
  · constructor <;> ring1
  constructor <;> constructor <;> ring1

/-- The five rational functions displayed in Exercise 9.3. -/
theorem exercise_9_3_first_five
    {K : Type*} [Algebra.Field.ExplicitField K] [Nontrivial K] (value : K) :
    Rational.Basic.turnRationalFunction 1 value = value ∧
      Rational.Basic.turnRationalFunction 2 value =
        (2 * value) / (1 - value ^ 2) ∧
      Rational.Basic.turnRationalFunction 3 value =
        (3 * value - value ^ 3) / (1 - 3 * value ^ 2) ∧
      Rational.Basic.turnRationalFunction 4 value =
        (4 * value - 4 * value ^ 3) /
          (1 - 6 * value ^ 2 + value ^ 4) ∧
      Rational.Basic.turnRationalFunction 5 value =
        (5 * value - 10 * value ^ 3 + value ^ 5) /
          (1 - 10 * value ^ 2 + 5 * value ^ 4) := by
  rcases turnRationalPair_first_five value with
    ⟨⟨numeratorOne, denominatorOne⟩,
      ⟨numeratorTwo, denominatorTwo⟩,
      ⟨numeratorThree, denominatorThree⟩,
      ⟨numeratorFour, denominatorFour⟩,
      numeratorFive, denominatorFive⟩
  unfold Rational.Basic.turnRationalFunction
  rw [numeratorOne, denominatorOne,
    numeratorTwo, denominatorTwo,
    numeratorThree, denominatorThree,
    numeratorFour, denominatorFour,
    numeratorFive, denominatorFive]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, -eq_self, -iff_self] 
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel (1 : K) one_ne_zero
    simpa only [one_mul, -eq_self, -iff_self]  using cancel
  rewrite [inverseOne]
  exact ⟨mul_one _, rfl, rfl, rfl, rfl⟩
end Purelib.Geometry.Trigonometry.Turn.Rational.Values

end
