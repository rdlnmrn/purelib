import mathlib.RFAP.PrimeBinomial
import mathlib.RFAP.QuadraticPair

/-!
# Prime powers in a finite quadratic pair

The quadratic-pair ring need not itself be a field.  Nevertheless, once the
base explicit field has prime characteristic, every interior binomial
coefficient is already zero in the base and hence in the pair.  This module
therefore lifts the finite prime-binomial law coordinatewise, without choosing
roots or enumerating either carrier.
-/

namespace RFAP
namespace QuadraticPair

variable {K : Type*} [ExplicitField K]

/-- Freshman's dream in an executable quadratic-pair ring over a base field of
prime characteristic.  Cancellation occurs only in the base field when the
coefficient equations are established. -/
theorem prime_add_pow
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (radialSquare : K)
    (left right : QuadraticPair K radialSquare) :
    (left + right) ^ prime = left ^ prime + right ^ prime := by
  apply RFAP.add_pow_eq_endpoints_of_interior_choose_cast_zero prime
    primeIsPrime.ne_zero
  intro index indexPositive indexBelow
  have baseCoefficientZero : (prime.choose index : K) = 0 :=
    RFAP.prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
      oneNonzero index indexPositive indexBelow
  calc
    (prime.choose index : QuadraticPair K radialSquare) =
        scalar (radialSquare := radialSquare) (prime.choose index : K) :=
      natCast_eq_scalar (prime.choose index)
    _ = scalar (radialSquare := radialSquare) 0 := by
      rw [baseCoefficientZero]
    _ = 0 := scalar_zero

/-- At an odd prime `p=2h+1`, the `p`th power of `c+j` has the two explicit
coordinates `c^p` and `(-b)^h`, where `j^2=-b`. -/
theorem scalar_add_generator_prime_pow
    (prime half : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (primeEquation : prime = half + half + 1)
    (center radialSquare : K) :
    let scalar := QuadraticPair.scalar (radialSquare := radialSquare)
    let generator := QuadraticPair.generator (K := K)
      (radialSquare := radialSquare)
    (scalar center + generator) ^ prime =
      scalar (center ^ prime) + scalar ((-radialSquare) ^ half) * generator := by
  dsimp only
  let scalar := QuadraticPair.scalar (radialSquare := radialSquare)
  let generator := QuadraticPair.generator (K := K)
    (radialSquare := radialSquare)
  have generatorPower :
      generator ^ prime = scalar ((-radialSquare) ^ half) * generator := by
    calc
      generator ^ prime = generator ^ (half + half + 1) := by
        rw [primeEquation]
      _ = generator ^ (half + half) * generator := by rw [pow_succ]
      _ = scalar ((-radialSquare) ^ half) * generator := by
        rw [QuadraticPair.generator_even_power]
  calc
    (scalar center + generator) ^ prime =
        scalar center ^ prime + generator ^ prime :=
      QuadraticPair.prime_add_pow prime primeIsPrime primeCastZero
        oneNonzero radialSquare (scalar center) generator
    _ = scalar (center ^ prime) + generator ^ prime := by
      rw [← QuadraticPair.scalar_pow]
    _ = scalar (center ^ prime) +
        scalar ((-radialSquare) ^ half) * generator := by
      rw [generatorPower]

end QuadraticPair
end RFAP
