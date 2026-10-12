module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Values
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Five

section

/-- Every nonzero root of `S₅` displays a square root `8s-5` of five.
This is the finite complete-square calculation used by Examples 14.5–14.7. -/
theorem nonzero_spreadPolynomial_five_root_gives_square_five
    {K : Type*} [ExplicitField K] [DecidableEq K]
    (value : K) (valueNonzero : value ≠ 0)
    (polynomialZero : Recurrence.Spread.Basic.spreadPolynomial 5 value = 0)
    (fiveNonzero : (5 : K) ≠ 0) : Algebra.Field.Squares.IsNonzeroSquare (5 : K) := by
  rw [Recurrence.Spread.Values.spreadPolynomial_five_formula] at polynomialZero
  have factorSquareZero :
      (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
    by_cases factorZero :
        (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
    · exact factorZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero valueNonzero factorZero)
          polynomialZero)
  have factorZero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {value : K} (squareZero :
    value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
    factorSquareZero
  let root := 8 * value - 5
  have rootSquare : root ^ 2 = (5 : K) := by
    calc
      root ^ 2 = 5 + 4 * (5 - 20 * value + 16 * value ^ 2) := by
        unfold root
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply fiveNonzero
    calc
      (5 : K) = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  exact ⟨root, rootNonzero, rootSquare.symm⟩

section

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] in
/-- Zero is the only root of the fifth spread polynomial when five is nonzero and not a nonzero square.

A hypothetical nonzero root would explicitly supply the square root `8 * value - 5`. -/
public theorem only_zero_of_five_nonsquare
    (fiveNonzero : (5 : K) ≠ 0)
    (fiveNotSquare : ¬ Algebra.Field.Squares.IsNonzeroSquare (5 : K))
    (value : K) (polynomialZero : Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · exact False.elim (fiveNotSquare
      (nonzero_spreadPolynomial_five_root_gives_square_five value
        valueZero polynomialZero fiveNonzero))

end

end

end Purelib.Polynomial.Recurrence.Spread.Roots.Five

end
