module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Quadratic (Pair)

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: odd spread-polynomial squares

Exercise 8.7 is proved in two nested executable quadratic-pair rings.  They
adjoin only the two formal relations needed by the finite binomial argument;
no root is selected in the coefficient field.
-/

namespace Purelib.Polynomial.Recurrence.Spread.QuadraticPair

variable {K : Type*} [ExplicitField K]

/-- Primitive-recursive spread polynomials commute with the scalar embedding
into a finite quadratic-pair ring.

Natural induction retains the original spread recurrence and quadratic-pair scalar embedding, including their
coefficients and multiplication. -/
theorem spreadPolynomial_quadraticPair_scalar
    {R : Type*} [CommRing R]
    (radialSquare value : R) (index : Nat) :
    Recurrence.Spread.Basic.spreadPolynomial index
        (Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare) value) =
      Algebra.Quadratic.Pair.scalar
        (Recurrence.Spread.Basic.spreadPolynomial index value) := by
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          simp only [Recurrence.Spread.Basic.spreadPolynomial_zero,
            Pair.scalar_zero, -eq_self, -iff_self]
          rfl
      | succ index =>
          cases index with
          | zero =>
              rfl
          | succ index =>
              change
                Recurrence.Spread.Basic.spreadPolynomial (index + 2)
                    (Algebra.Quadratic.Pair.scalar value) =
                  Algebra.Quadratic.Pair.scalar
                    (Recurrence.Spread.Basic.spreadPolynomial (index + 2) value)
              rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
                Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
              rw [inductionHypothesis (index + 1) (by omega0),
                inductionHypothesis index (by omega0)]
              rw [Pair.two_eq_scalar]
              apply Algebra.Quadratic.Pair.ext <;>
                simp only [Algebra.Quadratic.Pair.mul_re,
                  Algebra.Quadratic.Pair.mul_im,
                  Algebra.Quadratic.Pair.add_re,
                  Algebra.Quadratic.Pair.add_im,
                  Algebra.Quadratic.Pair.sub_re,
                  Algebra.Quadratic.Pair.sub_im,
                  Pair.scalar_re,
                  Pair.scalar_im,
                  Algebra.Quadratic.Pair.one_re,
                  Algebra.Quadratic.Pair.one_im]
              all_goals ring1

end Purelib.Polynomial.Recurrence.Spread.QuadraticPair

end
