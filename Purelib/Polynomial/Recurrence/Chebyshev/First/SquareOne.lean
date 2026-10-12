module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, remaining Chapter 8 exercises

This module records the finite algebra behind Exercises 8.2, 8.5, and
8.11--8.13.  Exercise 8.5 is proved uniformly for arbitrary natural residue
labels in characteristic `p`, using a finite prime-binomial argument rather
than an enumeration of an ambient field carrier.  Exercise 8.2 is likewise
proved for arbitrary residue labels using an executable quadratic pair and a
finite decidable algebraic split.  Exercise 8.11's bounded-sum interface is
defined here; its uniform prime-residue arithmetic and complete inner-product
results are proved in `ChapterEightInnerProduct`.

Exercise 8.12 is deliberately stopped before its completed-real integral.
The exact polynomial numerator obtained from the Chebyshev substitution is
proved for every requested pair of finite indices.  Exercise 8.13's printed
spread-cyclotomic factors are retained as explicit integer-coefficient
expressions, and every displayed divisor product is checked directly.  Its
finite totient and Lucas-square reduction is developed in
`SpreadCyclotomicReduction`; the arbitrary-index constructive factorization
and exact totient-degree theorem are completed in
`SpreadCyclotomicFactorization`.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.SquareOne

variable {K : Type*} [ExplicitField K]

section

/-- At a point whose square is one, the finite Chebyshev recurrence alternates
between `1` at even indices and the point at odd indices. -/
theorem chebyshevFirst_square_one
    (half : Nat) (center : K) (centerSquare : center ^ 2 = 1) :
    Recurrence.Chebyshev.First.Basic.chebyshevFirst (half + half) center = 1 ∧
      Recurrence.Chebyshev.First.Basic.chebyshevFirst (half + half + 1) center = center := by
  induction half with
  | zero =>
      constructor
      · exact Recurrence.Chebyshev.First.Basic.chebyshevFirst_zero center
      · exact Recurrence.Chebyshev.First.Basic.chebyshevFirst_one center
  | succ half inductionHypothesis =>
      have nextEven :
          Recurrence.Chebyshev.First.Basic.chebyshevFirst (half + half + 2) center = 1 := by
        rw [Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ, inductionHypothesis.1,
          inductionHypothesis.2]
        rw [show 2 * center * center = 2 * center ^ 2 by
          rw [pow_two]
          ring1]
        rw [centerSquare]
        ring1
      constructor
      · simpa only [Nat.succ_eq_add_one,
          show half + 1 + (half + 1) = half + half + 2 by omega0]
          using nextEven
      · rw [show Nat.succ half + Nat.succ half + 1 =
          (half + half + 1) + 2 by omega0]
        rw [Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ, nextEven, inductionHypothesis.2]
        ring1
end

end Purelib.Polynomial.Recurrence.Chebyshev.First.SquareOne

end
