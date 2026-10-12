module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Stars.Regular.OrderFive.Construction
import Purelib.Geometry.Plane.Line.Spread.Realization
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Iteration.Spread
public import Purelib.Geometry.Stars.Regular.OrderFive.Basic
import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Values
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Iteration

open Purelib.Geometry.Plane.Reflection.Iteration.Spread

open Purelib.Geometry.Stars.Regular

open Purelib.Geometry.Stars.Regular.OrderFive

open Purelib.Polynomial.Recurrence

open Purelib.Polynomial.Recurrence.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

namespace Purelib.Geometry.Stars.Regular.OrderFive.Classification

variable {K : Type*} [ExplicitField K]

/-- A regular five-star supplies a nonzero square root of five and a second square witness.

The adjacent spread yields a root `r` with `r² = 5` and square `2(5-r)`, assuming two is nonzero. -/
theorem order_five_star_parameters [Nontrivial K]
  [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (star : OrderFive.Basic.RegularFiveStar K) : OrderFive.Basic.OrderFiveStarParameters (K := K) := by
  let initial := star.initialPair
  let s := (ReflectionPair.adjacentSpread initial)
  have sNonzero : s ≠ 0 := by
    intro sZero
    apply star.line₀Line₁Nonparallel
    exact (Spread.spread_eq_zero_iff_parallel star.line₀ star.line₁
      star.line₀NonNull star.line₁NonNull).1 sZero
  have closingParallel :
      initial.previous.Parallel (Iteration.reflectionLineAt initial 5) := by
    apply Plane.Line.parallel_symm
    exact Relations.line_parallel_of_equivalent star.lineAtFive_equivalent
  have closingSpreadZero :
      Spread.spread initial.previous (Iteration.reflectionLineAt initial 5)
          initial.previousNonNull (Iteration.reflectionLineAt_nonNull initial 5) = 0 :=
    (Spread.spread_eq_zero_iff_parallel initial.previous
      (Iteration.reflectionLineAt initial 5) initial.previousNonNull
      (Iteration.reflectionLineAt_nonNull initial 5)).2 closingParallel
  have polynomialValue := Spread.consecutive_spreads initial
    star.line₀Line₁Nonparallel twoNonzero 5
  have polynomialZero : Spread.Basic.spreadPolynomial 5 s = 0 := by
    calc
      Spread.Basic.spreadPolynomial 5 s =
          Spread.spread initial.previous (Iteration.reflectionLineAt initial 5)
            initial.previousNonNull (Iteration.reflectionLineAt_nonNull initial 5) :=
        polynomialValue.symm
      _ = 0 := closingSpreadZero
  rw [Values.spreadPolynomial_five_formula] at polynomialZero
  have factorSquareZero : (5 - 20 * s + 16 * s ^ 2) ^ 2 = 0 := by
    by_cases zero : (5 - 20 * s + 16 * s ^ 2) ^ 2 = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero sNonzero zero) polynomialZero)
  have factorZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) (squareZero :
    value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
    (5 - 20 * s + 16 * s ^ 2) factorSquareZero
  let root := 8 * s - 5
  have rootSquare : root ^ 2 = 5 := by
    calc
      root ^ 2 = 5 + 4 * (5 - 20 * s + 16 * s ^ 2) := by
        unfold root
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have eightNonzero := (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.eight_ne_zero (K := K) twoNonzero : (8 : K) ≠ 0)) twoNonzero
  have eightS : (8 : K) * s = 5 + root := by
    unfold root
    ring1
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    have fiveZero : (5 : K) = 0 := by
      calc
        (5 : K) = root ^ 2 := rootSquare.symm
        _ = 0 := by rw [rootZero]; ring1
    apply (ExplicitField.mul_ne_zero eightNonzero sNonzero)
    calc
      (8 : K) * s = 5 + root := eightS
      _ = 0 := by rw [fiveZero, rootZero]; ring1
  rcases Realization.spread_isSpreadNumber initial.previous initial.current
      initial.previousNonNull initial.currentNonNull with
    ⟨spreadRoot, spreadSquare⟩
  change s * (1 - s) = spreadRoot ^ 2 at spreadSquare
  have parameterSquare :
      2 * (5 - root) = (8 * spreadRoot) ^ 2 := by
    calc
      2 * (5 - root) =
          64 * (s * (1 - s)) +
            4 * (5 - 20 * s + 16 * s ^ 2) := by
              unfold root
              ring1
      _ = 64 * (s * (1 - s)) := by rw [factorZero]; ring1
      _ = 64 * spreadRoot ^ 2 := by rw [spreadSquare]
      _ = (8 * spreadRoot) ^ 2 := by ring1
  exact ⟨root, rootNonzero, rootSquare,
    ⟨8 * spreadRoot, parameterSquare⟩⟩

/-- Theorem 96 (Order five star): a regular five-star exists exactly when there is a nonzero square root `r` of `5` for
which `2(5-r)` is a square. Characteristic two is excluded explicitly because the five printed line representatives then
collapse. -/
theorem order_five_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (OrderFive.Basic.RegularFiveStar K) ↔ OrderFive.Basic.OrderFiveStarParameters (K := K) := by
  constructor
  · rintro ⟨star⟩
    exact order_five_star_parameters twoNonzero star
  · rintro ⟨root, rootNonzero, rootSquare, spreadRoot,
      parameterSquare⟩
    exact ⟨Construction.orderFiveStar root spreadRoot rootNonzero rootSquare
      parameterSquare.symm twoNonzero⟩

end Purelib.Geometry.Stars.Regular.OrderFive.Classification

end
