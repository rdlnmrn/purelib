module
import Purelib.Geometry.Stars.Regular.OrderSeven.Construction
import Purelib.Geometry.Plane.Line.Spread.Realization
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Iteration.Spread
public import Purelib.Geometry.Stars.Regular.OrderSeven.Basic
import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Values
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Iteration

open Purelib.Geometry.Plane.Reflection.Iteration.Spread

open Purelib.Geometry.Stars.Regular

open Purelib.Geometry.Stars.Regular.OrderSeven

open Purelib.Polynomial.Recurrence

open Purelib.Polynomial.Recurrence.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

namespace Purelib.Geometry.Stars.Regular.OrderSeven.Classification

variable {K : Type*} [ExplicitField K]

/-- A regular seven-star supplies a nonzero cubic root with square complementary product.

Its adjacent spread satisfies `7 - 56s + 112s² - 64s³ = 0` and `s(1-s)` is a square, assuming two is nonzero. -/
theorem order_seven_star_parameters [Nontrivial K]
  [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (star : OrderSeven.Basic.RegularSevenStar K) : OrderSeven.Basic.OrderSevenStarParameters (K := K) := by
  let value := (ReflectionPair.adjacentSpread star.initial)
  have adjacentNonparallel :
      ¬ star.initial.previous.Parallel star.initial.current := by
    have firstSecond := star.pairwiseNonparallel
      (0 : Fin 7) (1 : Fin 7) (by decide)
    have zeroValue : (0 : Fin 7).val = 0 := rfl
    have oneValue : (1 : Fin 7).val = 1 := rfl
    rw [zeroValue, oneValue] at firstSecond
    simpa only [Iteration.reflectionLineAt_zero,
      show Iteration.reflectionLineAt star.initial 1 = star.initial.current by rfl]
      using firstSecond
  have valueNonzero : value ≠ 0 := by
    intro valueZero
    apply adjacentNonparallel
    exact (Spread.spread_eq_zero_iff_parallel star.initial.previous
      star.initial.current star.initial.previousNonNull
      star.initial.currentNonNull).1 valueZero
  have closingParallel :
      star.initial.previous.Parallel (Iteration.reflectionLineAt star.initial 7) := by
    apply Plane.Line.parallel_symm
    exact Relations.line_parallel_of_equivalent star.closesAtSeven
  have closingSpreadZero :
      Spread.spread star.initial.previous (Iteration.reflectionLineAt star.initial 7)
          star.initial.previousNonNull
          (Iteration.reflectionLineAt_nonNull star.initial 7) = 0 :=
    (Spread.spread_eq_zero_iff_parallel star.initial.previous
      (Iteration.reflectionLineAt star.initial 7) star.initial.previousNonNull
      (Iteration.reflectionLineAt_nonNull star.initial 7)).2 closingParallel
  have polynomialValue := Spread.consecutive_spreads star.initial
    adjacentNonparallel twoNonzero 7
  have polynomialZero : Spread.Basic.spreadPolynomial 7 value = 0 := by
    calc
      Spread.Basic.spreadPolynomial 7 value =
          Spread.spread star.initial.previous (Iteration.reflectionLineAt star.initial 7)
            star.initial.previousNonNull
            (Iteration.reflectionLineAt_nonNull star.initial 7) := polynomialValue.symm
      _ = 0 := closingSpreadZero
  rw [Values.spreadPolynomial_seven_formula] at polynomialZero
  let cubic :=
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3
  have cubicSquareZero : cubic ^ 2 = 0 := by
    by_cases zero : cubic ^ 2 = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero valueNonzero zero) polynomialZero)
  have cubicZero : cubic = 0 := by
    by_cases zero : cubic = 0
    · exact zero
    · exact False.elim ((ExplicitField.square_nonzero_of_nonzero zero) cubicSquareZero)
  rcases Realization.spread_isSpreadNumber star.initial.previous star.initial.current
      star.initial.previousNonNull star.initial.currentNonNull with
    ⟨spreadRoot, spreadSquare⟩
  exact ⟨value, valueNonzero, cubicZero, spreadRoot, spreadSquare⟩

/-- Theorem 97 (Order seven star): a regular seven-star exists exactly when the printed cubic has a nonzero root `s` and
`s(1-s)` is a square. -/
theorem order_seven_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (OrderSeven.Basic.RegularSevenStar K) ↔ OrderSeven.Basic.OrderSevenStarParameters (K := K) := by
  constructor
  · rintro ⟨star⟩
    exact order_seven_star_parameters twoNonzero star
  · rintro ⟨value, valueNonzero, cubicZero, spreadRoot, spreadSquare⟩
    exact ⟨Construction.orderSevenStar value spreadRoot valueNonzero cubicZero
      spreadSquare.symm twoNonzero⟩

end Purelib.Geometry.Stars.Regular.OrderSeven.Classification

end
