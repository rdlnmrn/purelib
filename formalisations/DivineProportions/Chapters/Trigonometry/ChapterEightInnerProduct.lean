module
import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Prime.Defs

open Purelib.Algebra

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace formalisations.DivineProportions.Chapters.Trigonometry.ChapterEightInnerProduct

variable {K : Type*} [Field.ExplicitField K]

namespace ExerciseEightEleven

/-- Exercise 8.11 in one finite statement: all requested bounded inner
products vanish except at index sums `p-1` and `p+1`, where their values are
respectively `-1/16` and `1/16`. -/
theorem exercise_8_11
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2) :
    ((first + second ≠ prime - 1 ∧ first + second ≠ prime + 1) →
        Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct (K := K) prime first second = 0) ∧
      (first + second = prime - 1 →
        Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct (K := K) prime first second =
          Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.lowerExceptionalValue) ∧
      (first + second = prime + 1 →
        Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct (K := K) prime first second =
          Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.upperExceptionalValue) := by
  constructor
  · intro regular
    exact Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct_zero prime first second
      primeIsPrime
      primeCastZero twoNonzero firstPositive secondPositive firstAtMost
        secondAtMost regular.1 regular.2
  · constructor
    · intro lower
      exact Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct_lower_exceptional prime first
        second
        primeIsPrime primeCastZero twoNonzero firstPositive secondPositive
          firstAtMost secondAtMost lower
    · intro upper
      exact Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct.spreadInnerProduct_upper_exceptional prime first
        second
        primeIsPrime primeCastZero twoNonzero firstPositive secondPositive
          firstAtMost secondAtMost upper

end ExerciseEightEleven

end formalisations.DivineProportions.Chapters.Trigonometry.ChapterEightInnerProduct

end
