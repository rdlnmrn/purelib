module

import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Negation
public import Mathlib.Algebra.Ring.Defs

/-!
# Constructive ring normalization regressions

The generic identities exercise the retained normalizer with quadratic and
odd powers. Their original scalar operations use owned proof-only adapters.
-/

namespace Test.Tactic.Ring

attribute [local instance high] Purelib.Algebra.Group.Negation.subNegZeroMonoid

/-- Ring normalization retains negative integer coefficients, multiplication and powers.

The generic commutative-ring identity checks the original quadratic expression
using direct certificates for its scalar operations and natural exponents. -/
public theorem ring1_regression {R : Type*} [CommRing R] (value : R) :
    (-((2 : Nat) : R)) * (value + 1) ^ 2 =
      -((2 : Nat) : R) * value ^ 2 - ((4 : Nat) : R) * value - ((2 : Nat) : R) := by
  ring0

/-- Cubic normalization uses direct odd-power certificates.

The generic commutative-ring expression includes the successor of a doubled
exponent. Its expansion checks the retained base, square and final factor. -/
public theorem odd_power_regression {R : Type*} [CommRing R] (value : R) :
    (value + 1) ^ 3 =
      value ^ 3 + ((3 : Nat) : R) * value ^ 2 + ((3 : Nat) : R) * value + 1 := by
  ring0

/-- Ring normalization retains natural-valued integer cast coefficients.

The original integer literal is cast through the supplied ring and used on both
sides of the polynomial identity, exercising the integer-cast certificate route.
-/
public theorem integer_cast_coefficient {R : Type*} [CommRing R] (value : R) :
    ((17 : Int) : R) * (value + 1) =
      ((17 : Int) : R) * value + ((17 : Int) : R) := by
  ring0

/-- Quantified integer-cast normalization retains arbitrary scalar binders.

The cast coefficient and each supplied scalar remain under their original
binders while the frontend reconstructs their polynomial equality.
-/
public theorem quantified_integer_cast_coefficient {R : Type*} [CommRing R] :
    ∀ first second : R,
      ((17 : Int) : R) * (first + second) =
        ((17 : Int) : R) * first + ((17 : Int) : R) * second := by
  intro first second
  ring0
/-- An arbitrary odd power retains its doubled exponent and final scalar factor.

The identity checks symbolic natural exponents in the semiring normalizer.
Both equal factors have the supplied exponent, and the remaining factor
accounts for its successor after doubling. -/
public theorem symbolic_odd_power {R : Type*} [CommSemiring R]
    (value : R) (exponent : Nat) :
    value ^ (exponent + exponent + 1) =
      value ^ exponent * value ^ exponent * value := by
  ring0

end Test.Tactic.Ring
