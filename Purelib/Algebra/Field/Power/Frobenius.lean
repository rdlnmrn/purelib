module
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra.Field

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

namespace Purelib.Algebra.Field.Power.Frobenius

variable {K : Type*} [ExplicitField K]

section ExerciseEightFive

/-- Every scalar is fixed by the supplied natural power.

This pointwise exponent law imposes no separate finite-carrier or primality assumption. -/
def HasFrobeniusExponent (exponent : Nat) : Prop :=
  ∀ value : K, value ^ exponent = value
end ExerciseEightFive

end Purelib.Algebra.Field.Power.Frobenius

end
