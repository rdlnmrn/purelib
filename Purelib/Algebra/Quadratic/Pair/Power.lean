module

public import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

/-!
# Powers of purely imaginary quadratic pairs

The retained pair with parameter one has generator square minus one. Even
and odd powers retain their original scalar and imaginary-coordinate formulas.
-/

namespace Purelib.Algebra.Quadratic.Pair.Power

open Purelib.Algebra
open Purelib.Algebra.Quadratic.Pair

/-- An even power of a purely imaginary pair is scalar.

For exponent twice the index, the scalar is the corresponding power of negative one times the input raised to that even
exponent. -/
public theorem pureImaginary_even_power
    {R : Type*} [CommRing R] (value : R) (index : Nat) :
    (⟨0, value⟩ : Pair R 1) ^ (index + index) =
      scalar
        ((-1 : R) ^ index * value ^ (index + index)) := by
  let generator := generator (K := R) (radialSquare := 1)
  have pairFactorization :
      (⟨0, value⟩ : Pair R 1) =
        generator * scalar value := by
    ext <;> simp only [generator, generator_re,
      generator_im, scalar_re,
      scalar_im, mul_re,
      mul_im]
    all_goals ring1
  rw [pairFactorization, Semiring.Normalization.product_pow,
    generator_even_power]
  rw [← scalar_pow,
    ← scalar_mul]

/-- An odd power of a purely imaginary pair is purely imaginary.

For exponent twice the index plus one, the imaginary coordinate is the corresponding power of negative one times the
input power. -/
public theorem pureImaginary_odd_power
    {R : Type*} [CommRing R] (value : R) (index : Nat) :
    (⟨0, value⟩ : Pair R 1) ^
        (index + index + 1) =
      ⟨0, (-1 : R) ^ index * value ^ (index + index + 1)⟩ := by
  rw [pow_succ, pureImaginary_even_power]
  ext
  · simp only [scalar_re,
      scalar_im, mul_re]
    ring1
  · simp only [scalar_re,
      scalar_im, mul_im]
    rw [pow_succ]
    ring1

end Purelib.Algebra.Quadratic.Pair.Power
