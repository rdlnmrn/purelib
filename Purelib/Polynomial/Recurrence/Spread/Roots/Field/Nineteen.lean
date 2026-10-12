module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

open Purelib.Polynomial

section
public section

/-!
# Divine Proportions, Chapter 2 finite-field examples

The source's characteristic-seven arithmetic and characteristic-nineteen
polynomial data are recorded by exact finite calculations.  The `S₅` table is
a literal list evaluation, not a claim that a list enumerates an ambient
carrier.  The characteristic-nineteen factorization is proved as a direct
polynomial identity; no carrier enumeration or root search is used.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Field.Nineteen

section

variable {K : Type*} [ExplicitField K] [Nontrivial K]

/-- Nine is nonzero when nineteen vanishes in a nontrivial explicit field. -/
private theorem nine_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (9 : K) ≠ 0 := by
  intro nineZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 19 - 2 * 9 := by ring1
    _ = 0 := by rw [nineteenZero, nineZero]; ring1

/-- Sixteen is nonzero when nineteen vanishes in a nontrivial explicit field. -/
private theorem sixteen_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (16 : K) ≠ 0 := by
  intro sixteenZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 6 * 16 - 5 * 19 := by ring1
    _ = 0 := by rw [nineteenZero, sixteenZero]; ring1

/-- Seven is nonzero when nineteen vanishes in a nontrivial explicit field. -/
private theorem seven_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (7 : K) ≠ 0 := by
  intro sevenZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 11 * 7 - 4 * 19 := by ring1
    _ = 0 := by rw [nineteenZero, sevenZero]; ring1

omit [Nontrivial K] in
/-- Factor the fifth spread polynomial when nineteen vanishes.

The factorization is nine times the coordinate and the squared factors at nine and sixteen; it requires no enumeration
of the coefficient field. -/
theorem example_2_18 (nineteenZero : (19 : K) = 0)
  (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value =
      9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 := by
  have quadraticFactor :
      5 - 20 * value + 16 * value ^ 2 =
        -3 * (value - 9) * (value - 16) := by
    calc
      5 - 20 * value + 16 * value ^ 2 =
          -3 * (value - 9) * (value - 16) +
            19 * (value ^ 2 - 5 * value + 23) := by ring1
      _ = -3 * (value - 9) * (value - 16) := by
        rw [nineteenZero]
        ring1
  calc
    Recurrence.Spread.Basic.spreadPolynomial 5 value =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
      simp only [Recurrence.Spread.Basic.spreadPolynomial]
      ring1
    _ = 9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 := by
      rw [quadraticFactor]
      ring1

/-- Example 2.18's complete zero classification.  The proof branches only on
the three displayed candidates; it never enumerates the coefficient field. -/
theorem example_2_18_zeroes [DecidableEq K]
    (nineteenZero : (19 : K) = 0) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value = 0 ↔
      value = 0 ∨ value = 9 ∨ value = 16 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    by_cases valueNine : value = 9
    · exact Or.inr (Or.inl valueNine)
    by_cases valueSixteen : value = 16
    · exact Or.inr (Or.inr valueSixteen)
    · have valueMinusNineNonzero : value - 9 ≠ 0 := by
        intro differenceZero
        exact valueNine (Group.eq_of_sub_eq_zero differenceZero)
      have valueMinusSixteenNonzero : value - 16 ≠ 0 := by
        intro differenceZero
        exact valueSixteen (Group.eq_of_sub_eq_zero differenceZero)
      have factoredNonzero :
          9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 ≠ 0 :=
        ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero
            (ExplicitField.mul_ne_zero nineNonzero valueZero)
            (ExplicitField.square_nonzero_of_nonzero valueMinusNineNonzero))
          (ExplicitField.square_nonzero_of_nonzero valueMinusSixteenNonzero)
      exact False.elim (factoredNonzero
        ((example_2_18 nineteenZero value).symm.trans polynomialZero))
  · intro alternatives
    rcases alternatives with valueZero | valueNine | valueSixteen
    · rw [example_2_18 nineteenZero value, valueZero]
      ring1
    · rw [example_2_18 nineteenZero value, valueNine]
      ring1
    · rw [example_2_18 nineteenZero value, valueSixteen]
      ring1

/-- The explicit nonvanishing cofactor certificate showing that zero has
multiplicity exactly one in Example 2.18. -/
theorem example_2_18_zero_multiplicity_one
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      Recurrence.Spread.Basic.spreadPolynomial 5 value =
        (value - 0) ^ 1 *
          (9 * (value - 9) ^ 2 * (value - 16) ^ 2)) ∧
      9 * ((0 : K) - 9) ^ 2 * ((0 : K) - 16) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sixteenNonzero := sixteen_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero nineNonzero
        (ExplicitField.square_nonzero_of_nonzero (by
          rw [zero_sub]
          exact (by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite [neg_neg,
            SubNegZeroMonoid.neg_zero] at restored; exact nineNonzero restored))))
      (ExplicitField.square_nonzero_of_nonzero (by
        rw [zero_sub]
        exact (by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite [neg_neg,
          SubNegZeroMonoid.neg_zero] at restored; exact sixteenNonzero restored)))

/-- The explicit nonvanishing cofactor certificate showing that nine has
multiplicity exactly two in Example 2.18. -/
theorem example_2_18_nine_multiplicity_two
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      Recurrence.Spread.Basic.spreadPolynomial 5 value =
        (value - 9) ^ 2 *
          (9 * value * (value - 16) ^ 2)) ∧
      (9 : K) * 9 * (9 - 16) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sevenNonzero := seven_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · have differenceNonzero : (9 : K) - 16 ≠ 0 := by
      intro differenceZero
      apply sevenNonzero
      calc
        (7 : K) = -(9 - 16) := by ring1
        _ = 0 := by rw [differenceZero]; ring1
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero nineNonzero nineNonzero)
      (ExplicitField.square_nonzero_of_nonzero differenceNonzero)

/-- The explicit nonvanishing cofactor certificate showing that sixteen has
multiplicity exactly two in Example 2.18. -/
theorem example_2_18_sixteen_multiplicity_two
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      Recurrence.Spread.Basic.spreadPolynomial 5 value =
        (value - 16) ^ 2 *
          (9 * value * (value - 9) ^ 2)) ∧
      (9 : K) * 16 * (16 - 9) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sixteenNonzero := sixteen_ne_zero_of_nineteen_eq_zero nineteenZero
  have sevenNonzero := seven_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · have differenceNonzero : (16 : K) - 9 ≠ 0 := by
      intro differenceZero
      apply sevenNonzero
      calc
        (7 : K) = 16 - 9 := by ring1
        _ = 0 := differenceZero
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero nineNonzero sixteenNonzero)
      (ExplicitField.square_nonzero_of_nonzero differenceNonzero)

end

end Purelib.Polynomial.Recurrence.Spread.Roots.Field.Nineteen

end

end
