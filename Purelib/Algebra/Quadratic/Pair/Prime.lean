module
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Binomial
public import Purelib.Algebra.Field.ExplicitField
import Purelib.NumberTheory.Prime.Binomial
public import Purelib.Algebra.Quadratic.Pair.Basic
public import Mathlib.Data.Nat.Prime.Defs

open Purelib.Algebra.Field
open Purelib

@[expose] public section

/-!
# Prime powers in a finite quadratic pair

The quadratic-pair ring need not itself be a field.  Nevertheless, once the
base explicit field has prime characteristic, every interior binomial
coefficient is already zero in the base and hence in the pair.  This module
therefore lifts the finite prime-binomial law coordinatewise, without choosing
roots or enumerating either carrier.
-/

namespace Purelib.Algebra.Quadratic.Pair

open Purelib.Algebra.Quadratic

variable {K : Type*} [ExplicitField K]

open Purelib.Algebra.Quadratic.Pair
/-- A prime power distributes over addition in the quadratic-pair ring.

The base explicit field has the supplied prime characteristic and nonzero one, so its interior binomial coefficients
vanish without assuming the pair ring is a field. -/
theorem prime_add_pow
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (radialSquare : K)
    (left right : Pair K radialSquare) :
    (left + right) ^ prime = left ^ prime + right ^ prime := open Purelib in open Purelib.NumberTheory in by
  apply Algebra.Binomial.add_pow_eq_endpoints_of_interior_choose_cast_zero prime
    (NumberTheory.Prime.ne_zero primeIsPrime)
  intro index indexPositive indexBelow
  have baseCoefficientZero : (prime.choose index : K) = 0 :=
    Prime.Binomial.prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
      oneNonzero index indexPositive indexBelow
  calc
    (prime.choose index : Pair K radialSquare) =
        scalar (radialSquare := radialSquare) (prime.choose index : K) :=
      Pair.natCast_eq_scalar (prime.choose index)
    _ = scalar (radialSquare := radialSquare) 0 := by
      rw [baseCoefficientZero]
    _ = 0 := Pair.scalar_zero

/-- Compute a scalar-plus-generator power at an explicitly odd prime.

The supplied half-index gives the prime as twice that index plus one; prime characteristic reduces the result to the
center power and a scalar power of the negative square parameter times the generator. -/
theorem scalar_add_generator_prime_pow
    (prime half : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (primeEquation : prime = half + half + 1)
    (center radialSquare : K) :
    let scalar := Pair.scalar (radialSquare := radialSquare)
    let generator := Pair.generator (K := K)
      (radialSquare := radialSquare)
    (scalar center + generator) ^ prime =
      scalar (center ^ prime) + scalar ((-radialSquare) ^ half) * generator := by
  dsimp only
  let scalar := Pair.scalar (radialSquare := radialSquare)
  let generator := Pair.generator (K := K)
    (radialSquare := radialSquare)
  have generatorPower :
      generator ^ prime = scalar ((-radialSquare) ^ half) * generator := by
    calc
      generator ^ prime = generator ^ (half + half + 1) := by
        rw [primeEquation]
      _ = generator ^ (half + half) * generator := by rw [pow_succ]
      _ = scalar ((-radialSquare) ^ half) * generator := by
        rw [Pair.generator_even_power]
  calc
    (scalar center + generator) ^ prime =
        scalar center ^ prime + generator ^ prime :=
      Pair.prime_add_pow prime primeIsPrime primeCastZero
        oneNonzero radialSquare (scalar center) generator
    _ = scalar (center ^ prime) + generator ^ prime := by
      rw [← Pair.scalar_pow]
    _ = scalar (center ^ prime) +
        scalar ((-radialSquare) ^ half) * generator := by
      rw [generatorPower]

end Purelib.Algebra.Quadratic.Pair

end
