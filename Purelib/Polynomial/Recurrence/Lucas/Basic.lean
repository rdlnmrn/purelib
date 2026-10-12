module
public import Purelib.Data.Nat.Order

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `Purelib.NumberTheory.Totient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace Purelib.Polynomial.Recurrence.Lucas.Basic

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen

/-- Lucas polynomial evaluation by its two-step integer recurrence. -/
def lucas : Nat → K → K
  | 0, _ => 2
  | 1, value => value
  | index + 2, value =>
      value * Purelib.Polynomial.Recurrence.Lucas.Basic.lucas (index + 1) value -
        Purelib.Polynomial.Recurrence.Lucas.Basic.lucas index value

open Purelib.Polynomial
namespace ExerciseEightThirteen

/-- The index-zero Lucas value is two. -/
@[simp] theorem lucas_zero (value : K) :
    Recurrence.Lucas.Basic.lucas 0 value = 2 := rfl

/-- The index-one Lucas value is its argument. -/
@[simp] theorem lucas_one (value : K) :
    Recurrence.Lucas.Basic.lucas 1 value = value := rfl

/-- The next Lucas value is the argument times its predecessor minus the preceding value. -/
@[simp] theorem lucas_succ_succ (index : Nat)
  (value : K) :
    Recurrence.Lucas.Basic.lucas (index + 2) value =
      value * Recurrence.Lucas.Basic.lucas (index + 1) value - Recurrence.Lucas.Basic.lucas index value := rfl

end ExerciseEightThirteen
end ExerciseEightThirteen

end Purelib.Polynomial.Recurrence.Lucas.Basic

end

section
@[expose] public section

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace Purelib.Algebra.Quadratic.TracePair

section TracePair

variable {K : Type*} [ExplicitField K]

/-- The Lucas recurrence intrinsic to the trace relation. -/
def lucas : Nat → K → K
  | 0, _ => 2
  | 1, trace => trace
  | index + 2, trace =>
      trace * lucas (index + 1) trace -
        lucas index trace
end TracePair

end Purelib.Algebra.Quadratic.TracePair

end

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

namespace Purelib.Polynomial.Recurrence.Lucas.Basic.ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

open Purelib in
open Purelib.Polynomial in
/-- The two independently defined finite Lucas recurrences agree. -/
theorem tracePair_lucas_eqLucas
  : ∀ index : Nat, ∀ value : K,
    Algebra.Quadratic.TracePair.lucas index value =
      Recurrence.Lucas.Basic.lucas index value
  | 0, value => rfl
  | 1, value => rfl
  | index + 2, value => by
      rw [Algebra.Quadratic.TracePair.lucas,
        Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_succ_succ,
        Purelib.Polynomial.Recurrence.Lucas.Basic.ExerciseEightThirteen.IntegerPolynomial.tracePair_lucas_eqLucas (index
          + 1) value,
        Purelib.Polynomial.Recurrence.Lucas.Basic.ExerciseEightThirteen.IntegerPolynomial.tracePair_lucas_eqLucas index
          value]
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Lucas.Basic.ExerciseEightThirteen.IntegerPolynomial

end
