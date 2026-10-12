module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Turn.Composition
public import Purelib.Geometry.Trigonometry.Turn.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

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

namespace Purelib.Geometry.Trigonometry.Turn.Rational.Iteration

/-- Wherever the two consecutive displayed denominators are nonzero, the finite rational functions obey the
turn-composition rule from Exercise 9.2. -/
theorem turnRationalFunction_succ
    {K : Type*} [Algebra.Field.ExplicitField K]
    (index : Nat) (value : K)
    (currentDenominatorNonzero :
      Rational.Basic.turnRationalDenominator index value ≠ 0)
    (nextDenominatorNonzero :
      Rational.Basic.turnRationalDenominator (index + 1) value ≠ 0) :
    Rational.Basic.turnRationalFunction (index + 1) value =
      Composition.turnComposition (Rational.Basic.turnRationalFunction index value) value := by
  let numerator := Rational.Basic.turnRationalNumerator index value
  let denominator := Rational.Basic.turnRationalDenominator index value
  let quotient := numerator / denominator
  have quotientCancel : quotient * denominator = numerator := by
    exact ExplicitField.div_mul_cancel numerator
      currentDenominatorNonzero
  have numeratorStep :
      Rational.Basic.turnRationalNumerator (index + 1) value =
        numerator + value * denominator := by
    exact Rational.Basic.turnRationalNumerator_succ index value
  have denominatorStep :
      Rational.Basic.turnRationalDenominator (index + 1) value =
        denominator - value * numerator := by
    exact Rational.Basic.turnRationalDenominator_succ index value
  have compositionProduct :
      denominator * (1 - quotient * value) =
        Rational.Basic.turnRationalDenominator (index + 1) value := by
    calc
      denominator * (1 - quotient * value) =
          denominator - value * (quotient * denominator) := by ring1
      _ = denominator - value * numerator := by rw [quotientCancel]
      _ = Rational.Basic.turnRationalDenominator (index + 1) value :=
        denominatorStep.symm
  have compositionDenominatorNonzero : 1 - quotient * value ≠ 0 := by
    intro zeroComposition
    apply nextDenominatorNonzero
    calc
      Rational.Basic.turnRationalDenominator (index + 1) value =
          denominator * (1 - quotient * value) := compositionProduct.symm
      _ = 0 := by rw [zeroComposition, mul_zero]
  unfold Rational.Basic.turnRationalFunction Composition.turnComposition
  change
    Rational.Basic.turnRationalNumerator (index + 1) value /
        Rational.Basic.turnRationalDenominator (index + 1) value =
      (quotient + value) / (1 - quotient * value)
  apply Ratio.ratio_eq_of_cross_product nextDenominatorNonzero
    compositionDenominatorNonzero
  rw [numeratorStep, denominatorStep]
  have quotientDifference : numerator - quotient * denominator = 0 := by
    rw [quotientCancel]
    ring1
  calc
    (numerator + value * denominator) * (1 - quotient * value) =
        (quotient + value) * (denominator - value * numerator) +
          (numerator - quotient * denominator) * (1 + value ^ 2) := by
      ring1
    _ = (quotient + value) * (denominator - value * numerator) := by
      rw [quotientDifference]
      ring1

/-- Primitive recursion for exactly the requested number of equal turn-compositions. -/
def iteratedTurnComposition
    {K : Type*} [ExplicitField K] : Nat → K → K
  | 0, _ => 0
  | index + 1, value =>
      Purelib.Geometry.Trigonometry.Turn.Composition.turnComposition
        (iteratedTurnComposition index value) value

/-- Finite composition meaning of Exercise 9.3. The premise exposes all and only the rational-function poles encountered
through the requested index. -/
theorem exercise_9_3_iteration
    {K : Type*} [Algebra.Field.ExplicitField K]
    (index : Nat) (value : K)
    (denominatorsNonzero : ∀ current : Nat, current ≤ index →
      Rational.Basic.turnRationalDenominator current value ≠ 0) :
    iteratedTurnComposition index value =
      Rational.Basic.turnRationalFunction index value := by
  induction index with
  | zero =>
      unfold iteratedTurnComposition Rational.Basic.turnRationalFunction
      rw [Rational.Basic.turnRationalNumerator_zero,
        ExplicitField.zero_div]
  | succ index inductionHypothesis =>
      change
        Composition.turnComposition (iteratedTurnComposition index value) value =
          Rational.Basic.turnRationalFunction (index + 1) value
      rw [inductionHypothesis (fun current currentBound =>
        denominatorsNonzero current (by omega0))]
      exact (turnRationalFunction_succ index value
        (denominatorsNonzero index (by omega0))
        (denominatorsNonzero (index + 1) (by omega0))).symm
end Purelib.Geometry.Trigonometry.Turn.Rational.Iteration

end
