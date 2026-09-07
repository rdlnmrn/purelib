import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadChebyshev
import DivineProportions.Trigonometry.SpreadCoefficient
import DivineProportions.Trigonometry.SpreadBinomial
import mathlib.RFAP.PrimeQuadraticPair

/-!
# Divine Proportions, remaining Chapter 8 exercises

This module records the finite algebra behind Exercises 8.2, 8.5, and
8.11--8.13.  Exercise 8.5 is proved uniformly for arbitrary natural residue
labels in characteristic `p`, using a finite prime-binomial argument rather
than an enumeration of an ambient field carrier.  Exercise 8.2 is likewise
proved for arbitrary residue labels using an executable quadratic pair and a
finite decidable algebraic split.  Exercise 8.11's bounded-sum interface is
defined here; its uniform prime-residue arithmetic and complete inner-product
theorem are proved in `ChapterEightInnerProduct`.

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

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace ExerciseEightTwo

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor * factor⁻¹) * value := by rw [factorCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem eq_of_mul_eq_mul_left
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have differenceZero : factor * (left - right) = 0 := by
    rw [mul_sub, productsEqual, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_mul_eq_zero_left factorNonzero differenceZero)

/-- The period proposed in Exercise 8.2, computed by ordinary finite natural
number arithmetic. -/
def gohPeriod (primeCardinality : Nat) : Nat :=
  (primeCardinality - 1) * (primeCardinality + 1) / 2

/-- For an odd number `p=2h+1`, Goh's displayed period is the ordinary
finite product `h(p+1)`.  This is the division-free form used by the power
calculation. -/
theorem gohPeriod_odd
    (prime half : Nat) (primeEquation : prime = half + half + 1) :
    gohPeriod prime = half * (prime + 1) := by
  subst prime
  unfold gohPeriod
  rw [show half + half + 1 - 1 = 2 * half by omega0]
  rw [show (2 * half) * (half + half + 1 + 1) =
      2 * (half * (half + half + 1 + 1)) by rw [mul_assoc]]
  exact Nat.mul_div_cancel_left _ (by decide : 0 < 2)

/-- At a point whose square is one, the finite Chebyshev recurrence alternates
between `1` at even indices and the point at odd indices. -/
theorem chebyshevFirst_square_one
    (half : Nat) (center : K) (centerSquare : center ^ 2 = 1) :
    chebyshevFirst (half + half) center = 1 ∧
      chebyshevFirst (half + half + 1) center = center := by
  induction half with
  | zero =>
      constructor
      · exact chebyshevFirst_zero center
      · exact chebyshevFirst_one center
  | succ half inductionHypothesis =>
      have nextEven :
          chebyshevFirst (half + half + 2) center = 1 := by
        rw [chebyshevFirst_succ_succ, inductionHypothesis.1,
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
        rw [chebyshevFirst_succ_succ, nextEven, inductionHypothesis.2]
        ring1

/-- Frobenius fixes the discriminant `c²-1` whenever it fixes `c`. -/
theorem square_sub_one_prime_pow
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (primeOdd : Odd prime) (center : K)
    (centerPower : center ^ prime = center) :
    (center ^ 2 - 1) ^ prime = center ^ 2 - 1 := by
  have squarePower : (center ^ 2) ^ prime = center ^ 2 := by
    calc
      (center ^ 2) ^ prime = center ^ (2 * prime) :=
        (pow_mul center 2 prime).symm
      _ = center ^ (prime * 2) := by
        congr 1
        omega0
      _ = (center ^ prime) ^ 2 := pow_mul center prime 2
      _ = center ^ 2 := by rw [centerPower]
  have negativeOnePower : (-1 : K) ^ prime = -1 := by
    rw [primeOdd.neg_pow, one_pow]
  calc
    (center ^ 2 - 1) ^ prime = (center ^ 2 + (-1)) ^ prime := by
      congr 1
      ring1
    _ = (center ^ 2) ^ prime + (-1 : K) ^ prime :=
      RFAP.prime_add_pow prime primeIsPrime primeCastZero oneNonzero
        (center ^ 2) (-1)
    _ = center ^ 2 - 1 := by rw [squarePower, negativeOnePower]; ring1

/-- The two Chebyshev seeds behind Goh's period.  The proof works in the
explicit quadratic pair generated by a root of `z²-2cz+1`.  Decidable equality
selects the three finite algebraic cases `c²-1=0`, Euler value `1`, and Euler
value `-1`; it does not enumerate the base field. -/
theorem prime_chebyshev_period_seeds
    [DecidableEq K]
    (prime half : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (primeEquation : prime = half + half + 1)
    (center : K) (centerPower : center ^ prime = center) :
    let period := half * (prime + 1)
    chebyshevFirst period center = 1 ∧
      chebyshevFirst (period + 1) center = center := by
  dsimp only
  have primeOdd : Odd prime := ⟨half, by omega0⟩
  let period := half * (prime + 1)
  let discriminant := center ^ 2 - 1
  by_cases discriminantZero : discriminant = 0
  · have centerSquare : center ^ 2 = 1 :=
      sub_eq_zero.mp discriminantZero
    let periodHalf := half * (half + 1)
    have periodEven : period = periodHalf + periodHalf := by
      unfold period periodHalf
      rw [primeEquation]
      calc
        half * (half + half + 1 + 1) =
            half * ((half + 1) + (half + 1)) := by
          congr 1
          omega0
        _ = half * (half + 1) + half * (half + 1) := by
          rw [Nat.mul_add]
    have squareSeeds := chebyshevFirst_square_one periodHalf center
      centerSquare
    rw [show half * (prime + 1) = periodHalf + periodHalf from periodEven]
    exact squareSeeds
  · let euler := discriminant ^ half
    have discriminantPower : discriminant ^ prime = discriminant := by
      unfold discriminant
      exact square_sub_one_prime_pow prime primeIsPrime primeCastZero
        oneNonzero primeOdd center centerPower
    have discriminantEulerSquare :
        discriminant * euler ^ 2 = discriminant ^ prime := by
      calc
        discriminant * euler ^ 2 =
            discriminant *
              (discriminant ^ half * discriminant ^ half) := by
          unfold euler
          rw [pow_two]
        _ = discriminant * discriminant ^ (half + half) := by
          rw [pow_add]
        _ = discriminant ^ (half + half + 1) := by
          rw [pow_succ']
        _ = discriminant ^ prime := by rw [primeEquation]
    have eulerSquare : euler ^ 2 = 1 := by
      apply sub_eq_zero.mp
      apply eq_zero_of_mul_eq_zero_left discriminantZero
      calc
        discriminant * (euler ^ 2 - 1) =
            discriminant * euler ^ 2 - discriminant := by ring1
        _ = discriminant ^ prime - discriminant := by
          rw [discriminantEulerSquare]
        _ = 0 := by rw [discriminantPower, sub_self]
    let radialSquare := 1 - center ^ 2
    let scalar := RFAP.QuadraticPair.scalar
      (radialSquare := radialSquare)
    let generator := RFAP.QuadraticPair.generator (K := K)
      (radialSquare := radialSquare)
    let positive := scalar center + generator
    let negative := scalar center - generator
    have negativeRadial : -radialSquare = discriminant := by
      unfold radialSquare discriminant
      ring1
    have generatorPower :
        generator ^ prime = scalar euler * generator := by
      calc
        generator ^ prime = generator ^ (half + half + 1) := by
          rw [primeEquation]
        _ = generator ^ (half + half) * generator := by rw [pow_succ]
        _ = scalar ((-radialSquare) ^ half) * generator := by
          unfold generator scalar
          rw [RFAP.QuadraticPair.generator_even_power]
        _ = scalar euler * generator := by
          rw [negativeRadial]
    have positivePrimePower :
        positive ^ prime = scalar center + scalar euler * generator := by
      calc
        positive ^ prime =
            (scalar center + generator) ^ prime := rfl
        _ = scalar center ^ prime + generator ^ prime :=
          RFAP.QuadraticPair.prime_add_pow prime primeIsPrime primeCastZero
            oneNonzero radialSquare (scalar center) generator
        _ = scalar (center ^ prime) + generator ^ prime := by
          rw [← RFAP.QuadraticPair.scalar_pow]
        _ = scalar center + scalar euler * generator := by
          rw [centerPower, generatorPower]
    have negativePrimePower :
        negative ^ prime = scalar center - scalar euler * generator := by
      calc
        negative ^ prime = (scalar center + -generator) ^ prime := by
          congr 1
        _ = scalar center ^ prime + (-generator) ^ prime :=
          RFAP.QuadraticPair.prime_add_pow prime primeIsPrime primeCastZero
            oneNonzero radialSquare (scalar center) (-generator)
        _ = scalar (center ^ prime) + -(generator ^ prime) := by
          rw [← RFAP.QuadraticPair.scalar_pow, primeOdd.neg_pow]
        _ = scalar center - scalar euler * generator := by
          rw [centerPower, generatorPower]
          ring1
    have conjugateProduct : positive * negative = 1 := by
      unfold positive negative scalar generator radialSquare
      apply RFAP.QuadraticPair.ext <;>
        simp only [RFAP.QuadraticPair.mul_re,
          RFAP.QuadraticPair.mul_im, RFAP.QuadraticPair.add_re,
          RFAP.QuadraticPair.add_im, RFAP.QuadraticPair.sub_re,
          RFAP.QuadraticPair.sub_im, RFAP.QuadraticPair.scalar_re,
          RFAP.QuadraticPair.scalar_im,
          RFAP.QuadraticPair.generator_re,
          RFAP.QuadraticPair.generator_im,
          RFAP.QuadraticPair.one_re, RFAP.QuadraticPair.one_im] <;>
        ring1
    have seedsOfUnitPowers
        (positivePeriod : positive ^ period = 1)
        (negativePeriod : negative ^ period = 1) :
        chebyshevFirst period center = 1 ∧
          chebyshevFirst (period + 1) center = center := by
      have periodTrace := chebyshevFirst_quadraticPair_trace
        period center radialSquare rfl
      change positive ^ period + negative ^ period =
        scalar (2 * chebyshevFirst period center) at periodTrace
      rw [positivePeriod, negativePeriod] at periodTrace
      have doubledPeriod := congrArg RFAP.QuadraticPair.re periodTrace
      unfold scalar at doubledPeriod
      simp only [RFAP.QuadraticPair.add_re, RFAP.QuadraticPair.one_re,
        RFAP.QuadraticPair.scalar_re] at doubledPeriod
      have doubledPeriodNormalized :
          2 * chebyshevFirst period center = 2 := by
        calc
          2 * chebyshevFirst period center = 1 + 1 :=
            doubledPeriod.symm
          _ = 2 := by ring1
      have periodSeed : chebyshevFirst period center = 1 := by
        apply eq_of_mul_eq_mul_left twoNonzero
        simpa only [mul_one] using doubledPeriodNormalized
      have nextTrace := chebyshevFirst_quadraticPair_trace
        (period + 1) center radialSquare rfl
      change positive ^ (period + 1) + negative ^ (period + 1) =
        scalar (2 * chebyshevFirst (period + 1) center) at nextTrace
      rw [pow_succ, pow_succ, positivePeriod, negativePeriod,
        one_mul, one_mul] at nextTrace
      have doubledNext := congrArg RFAP.QuadraticPair.re nextTrace
      unfold positive negative scalar at doubledNext
      simp only [RFAP.QuadraticPair.add_re, RFAP.QuadraticPair.sub_re,
        RFAP.QuadraticPair.scalar_re]
        at doubledNext
      have doubledNextNormalized :
          2 * chebyshevFirst (period + 1) center = 2 * center := by
        calc
          2 * chebyshevFirst (period + 1) center =
              (center + 0) + (center - 0) := doubledNext.symm
          _ = 2 * center := by ring1
      have nextSeed : chebyshevFirst (period + 1) center = center := by
        apply eq_of_mul_eq_mul_left twoNonzero
        exact doubledNextNormalized
      exact ⟨periodSeed, nextSeed⟩
    by_cases eulerOne : euler = 1
    · have positiveFixed : positive ^ prime = positive := by
        rw [positivePrimePower, eulerOne]
        unfold positive scalar
        rw [
          RFAP.QuadraticPair.scalar_one, one_mul]
      have negativeFixed : negative ^ prime = negative := by
        rw [negativePrimePower, eulerOne]
        unfold negative scalar
        rw [
          RFAP.QuadraticPair.scalar_one, one_mul]
      have positivePeriodBase : positive ^ (prime - 1) = 1 := by
        calc
          positive ^ (prime - 1) =
              positive ^ (prime - 1) * (positive * negative) := by
            rw [conjugateProduct, mul_one]
          _ = (positive ^ (prime - 1) * positive) * negative := by ring1
          _ = positive ^ prime * negative := by
            rw [← pow_succ]
            congr 2
            omega0
          _ = positive * negative := by rw [positiveFixed]
          _ = 1 := conjugateProduct
      have negativePeriodBase : negative ^ (prime - 1) = 1 := by
        calc
          negative ^ (prime - 1) =
              negative ^ (prime - 1) * (positive * negative) := by
            rw [conjugateProduct, mul_one]
          _ = (negative ^ (prime - 1) * negative) * positive := by ring1
          _ = negative ^ prime * positive := by
            rw [← pow_succ]
            congr 2
            omega0
          _ = negative * positive := by rw [negativeFixed]
          _ = 1 := by rw [mul_comm, conjugateProduct]
      have periodAsMinus : period = (prime - 1) * (half + 1) := by
        unfold period
        calc
          half * (prime + 1) =
              half * ((half + 1) + (half + 1)) := by
            congr 1
            omega0
          _ = half * (half + 1) + half * (half + 1) := by
            rw [Nat.mul_add]
          _ = (half + half) * (half + 1) := by
            rw [Nat.add_mul]
          _ = (prime - 1) * (half + 1) := by
            congr 1
            omega0
      apply seedsOfUnitPowers
      · rw [periodAsMinus, pow_mul, positivePeriodBase, one_pow]
      · rw [periodAsMinus, pow_mul, negativePeriodBase, one_pow]
    · have eulerProductZero : (euler - 1) * (euler + 1) = 0 := by
        rw [show (euler - 1) * (euler + 1) = euler ^ 2 - 1 by ring1,
          eulerSquare, sub_self]
      have eulerMinusOneNonzero : euler - 1 ≠ 0 :=
        sub_ne_zero.mpr eulerOne
      have eulerPlusOneZero : euler + 1 = 0 :=
        eq_zero_of_mul_eq_zero_left eulerMinusOneNonzero eulerProductZero
      have eulerNegativeOne : euler = -1 := by
        calc
          euler = (euler + 1) - 1 := by ring1
          _ = -1 := by rw [eulerPlusOneZero]; ring1
      have positiveConjugate : positive ^ prime = negative := by
        rw [positivePrimePower, eulerNegativeOne]
        unfold negative scalar
        rw [
          RFAP.QuadraticPair.scalar_neg,
          RFAP.QuadraticPair.scalar_one]
        ring1
      have negativeConjugate : negative ^ prime = positive := by
        rw [negativePrimePower, eulerNegativeOne]
        unfold positive scalar
        rw [
          RFAP.QuadraticPair.scalar_neg,
          RFAP.QuadraticPair.scalar_one]
        ring1
      have positivePeriodBase : positive ^ (prime + 1) = 1 := by
        rw [pow_succ, positiveConjugate, mul_comm, conjugateProduct]
      have negativePeriodBase : negative ^ (prime + 1) = 1 := by
        rw [pow_succ, negativeConjugate, conjugateProduct]
      apply seedsOfUnitPowers
      · rw [show period = (prime + 1) * half by
          unfold period
          exact Nat.mul_comm _ _, pow_mul, positivePeriodBase, one_pow]
      · rw [show period = (prime + 1) * half by
          unfold period
          exact Nat.mul_comm _ _, pow_mul, negativePeriodBase, one_pow]

/-- Exercise 8.2 reduces to two explicitly checkable recurrence seeds.  Once
the prime-field calculation supplies these two identities at the proposed
period, the second-order recurrence proves every requested index without an
unbounded sequence. -/
theorem exercise_8_2_from_finite_seeds
    (primeCardinality index : Nat) (value : K)
    (zeroSeed :
      spreadPolynomial (gohPeriod primeCardinality) value = 0)
    (oneSeed :
      spreadPolynomial (gohPeriod primeCardinality + 1) value = value) :
    spreadPolynomial (index + gohPeriod primeCardinality) value =
      spreadPolynomial index value :=
  spreadPolynomial_period (gohPeriod primeCardinality) value
    zeroSeed oneSeed index

/-- Exercise 8.2 at the constructive finite-field boundary.  For every
natural residue label in an odd prime characteristic with decidable equality,
the spread-polynomial orbit has Goh's period `(p-1)(p+1)/2`.  The proof never
lists the elements of the field; it uses only the supplied residue, finite
prime-binomial arithmetic, and the executable quadratic pair. -/
theorem exercise_8_2_prime_residue
    [DecidableEq K]
    (prime residue index : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    spreadPolynomial (index + gohPeriod prime) (residue : K) =
      spreadPolynomial index (residue : K) := by
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneEqualsZero
    apply twoNonzero
    rw [← one_add_one_eq_two, oneEqualsZero, zero_add]
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have primeOdd : Odd prime := primeIsPrime.odd_of_ne_two primeNotTwo
  rcases primeOdd with ⟨half, oddEquation⟩
  have primeEquation : prime = half + half + 1 := by omega0
  let value : K := residue
  let center : K := 1 - 2 * value
  have valuePower : value ^ prime = value := by
    unfold value
    exact RFAP.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero
      residue
  have twoPower : (2 : K) ^ prime = 2 := by
    simpa only [Nat.cast_ofNat] using
      (RFAP.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero 2 :
        ((2 : Nat) : K) ^ prime = ((2 : Nat) : K))
  have centerPower : center ^ prime = center := by
    have primeOddPower : Odd prime :=
      primeIsPrime.odd_of_ne_two primeNotTwo
    calc
      center ^ prime = (1 + -(2 * value)) ^ prime := by
        congr 1
        unfold center
        ring1
      _ = 1 ^ prime + (-(2 * value)) ^ prime :=
        RFAP.prime_add_pow prime primeIsPrime primeCastZero oneNonzero 1
          (-(2 * value))
      _ = 1 - (2 * value) ^ prime := by
        rw [one_pow, primeOddPower.neg_pow]
        ring1
      _ = 1 - 2 * value ^ prime := by rw [mul_pow, twoPower]
      _ = center := by rw [valuePower]
  have chebyshevSeeds := prime_chebyshev_period_seeds
    prime half primeIsPrime primeCastZero oneNonzero twoNonzero
    primeEquation center centerPower
  have periodEquation : gohPeriod prime = half * (prime + 1) :=
    gohPeriod_odd prime half primeEquation
  have zeroSeed : spreadPolynomial (gohPeriod prime) value = 0 := by
    have doubledZero :
        2 * spreadPolynomial (gohPeriod prime) value = 0 := by
      calc
        2 * spreadPolynomial (gohPeriod prime) value =
            1 - chebyshevFirst (gohPeriod prime) center := by
          unfold center
          exact exercise_8_4_cleared (gohPeriod prime) value
        _ = 0 := by rw [periodEquation, chebyshevSeeds.1]; ring1
    exact eq_zero_of_mul_eq_zero_left twoNonzero doubledZero
  have oneSeed : spreadPolynomial (gohPeriod prime + 1) value = value := by
    have doubledEqual :
        2 * spreadPolynomial (gohPeriod prime + 1) value = 2 * value := by
      calc
        2 * spreadPolynomial (gohPeriod prime + 1) value =
            1 - chebyshevFirst (gohPeriod prime + 1) center := by
          unfold center
          exact exercise_8_4_cleared (gohPeriod prime + 1) value
        _ = 1 - center := by
          rw [periodEquation, chebyshevSeeds.2]
        _ = 2 * value := by unfold center; ring1
    exact eq_of_mul_eq_mul_left twoNonzero doubledEqual
  change spreadPolynomial (index + gohPeriod prime) value =
    spreadPolynomial index value
  exact exercise_8_2_from_finite_seeds prime index value zeroSeed oneSeed

end ExerciseEightTwo

namespace ExerciseEightFive

/-- A finite Frobenius certificate at the requested exponent.  It carries no
field enumeration: callers supply the pointwise power law actually used. -/
def HasFrobeniusExponent (exponent : Nat) : Prop :=
  ∀ value : K, value ^ exponent = value

/-- The second finite ingredient in the Chebyshev proof of Exercise 8.5:
at the requested prime index, the Chebyshev recurrence agrees pointwise with
the corresponding power map. -/
def ChebyshevAgreesWithPower (exponent : Nat) : Prop :=
  ∀ value : K, chebyshevFirst exponent value = value ^ exponent

/-- Exercise 8.5 from its two finite prime-field arithmetic inputs.  The
proof itself is exactly the source's Chebyshev reduction, with cancellation
of `2` exposed. -/
theorem exercise_8_5_from_frobenius
    (primeCardinality : Nat) (twoNonzero : (2 : K) ≠ 0)
    (chebyshevPower : ChebyshevAgreesWithPower (K := K) primeCardinality)
    (frobenius : HasFrobeniusExponent (K := K) primeCardinality)
    (value : K) :
    spreadPolynomial primeCardinality value = value := by
  have traceFixed :
      chebyshevFirst primeCardinality (1 - 2 * value) =
        1 - 2 * value := by
    calc
      chebyshevFirst primeCardinality (1 - 2 * value) =
          (1 - 2 * value) ^ primeCardinality :=
        chebyshevPower (1 - 2 * value)
      _ = 1 - 2 * value := frobenius (1 - 2 * value)
  have doubled : 2 * spreadPolynomial primeCardinality value = 2 * value := by
    calc
      2 * spreadPolynomial primeCardinality value =
          1 - chebyshevFirst primeCardinality (1 - 2 * value) :=
        exercise_8_4_cleared primeCardinality value
      _ = 2 * value := by rw [traceFixed]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    spreadPolynomial primeCardinality value =
        (2 * spreadPolynomial primeCardinality value) * (2 : K)⁻¹ := by
      calc
        spreadPolynomial primeCardinality value =
            spreadPolynomial primeCardinality value * 1 := by ring1
        _ = spreadPolynomial primeCardinality value *
              ((2 : K) * (2 : K)⁻¹) := by rw [twoCancel]
        _ = (2 * spreadPolynomial primeCardinality value) *
              (2 : K)⁻¹ := by ring1
    _ = (2 * value) * (2 : K)⁻¹ := by rw [doubled]
    _ = value := by
      calc
        (2 * value) * (2 : K)⁻¹ =
            value * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value := by rw [twoCancel]; ring1

/-- At an odd prime index, every nonconstant term in the finite spread
binomial expansion vanishes in characteristic `p`. -/
theorem spreadBinomialExpansion_prime_odd
    (prime half : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0)
    (oneNonzero : (1 : K) ≠ 0)
    (primeEquation : prime = half + half + 1)
    (center radialSquare : K) :
    spreadBinomialExpansion prime (half + 1) center radialSquare =
      center ^ prime := by
  have firstTerm :
      spreadBinomialTerm prime center radialSquare 0 = center ^ prime := by
    unfold spreadBinomialTerm
    simp only [zero_add, Nat.sub_zero, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, mul_one]
  have tailTermZero (index : Nat) (indexBelow : index < half) :
      spreadBinomialTerm prime center radialSquare (index + 1) = 0 := by
    let coefficientIndex := (index + 1) + (index + 1)
    have coefficientPositive : coefficientIndex ≠ 0 := by
      unfold coefficientIndex
      omega0
    have coefficientBelow : coefficientIndex < prime := by
      unfold coefficientIndex
      omega0
    have coefficientZero : (prime.choose coefficientIndex : K) = 0 :=
      RFAP.prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
        oneNonzero coefficientIndex coefficientPositive coefficientBelow
    unfold spreadBinomialTerm
    change
      (-radialSquare) ^ (index + 1) *
          center ^ (prime - coefficientIndex) *
            (prime.choose coefficientIndex : K) = 0
    rw [coefficientZero, mul_zero]
  have tailZero :
      RFAP.finitePrefixSum half (fun index =>
        spreadBinomialTerm prime center radialSquare (index + 1)) = 0 := by
    calc
      RFAP.finitePrefixSum half (fun index =>
          spreadBinomialTerm prime center radialSquare (index + 1)) =
        RFAP.finitePrefixSum half (fun _ : Nat => (0 : K)) := by
          apply RFAP.finitePrefixSum_congr
          intro index indexBelow
          exact tailTermZero index indexBelow
      _ = 0 := RFAP.finitePrefixSum_zero_values half
  unfold spreadBinomialExpansion
  rw [RFAP.finitePrefixSum_succ, firstTerm, tailZero, add_zero]

/-- Exercise 8.5 at the exact finite boundary: every natural residue label in
characteristic `p` is fixed by the `p`th spread polynomial.  This quantifies
over the residue data directly and makes no claim that a list enumerates an
ambient field carrier. -/
theorem exercise_8_5_prime_residue
    (prime residue : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    spreadPolynomial prime (residue : K) = (residue : K) := by
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneEqualsZero
    apply twoNonzero
    rw [← one_add_one_eq_two, oneEqualsZero, zero_add]
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have primeOdd : Odd prime := primeIsPrime.odd_of_ne_two primeNotTwo
  rcases primeOdd with ⟨half, oddEquation⟩
  have primeEquation : prime = half + half + 1 := by omega0
  let value : K := residue
  let center : K := 1 - 2 * value
  let radialSquare : K := 4 * value * (1 - value)
  have binomialIdentity :
      1 - 2 * spreadPolynomial prime value =
        spreadBinomialExpansion prime (half + 1) center radialSquare := by
    have source := exercise_8_6_odd half value twoNonzero
    simpa only [primeEquation, center, radialSquare] using source
  have expansionCollapse :
      spreadBinomialExpansion prime (half + 1) center radialSquare =
        center ^ prime :=
    spreadBinomialExpansion_prime_odd prime half primeIsPrime primeCastZero
      oneNonzero primeEquation center radialSquare
  have twoPower : (2 : K) ^ prime = 2 := by
    simpa only [Nat.cast_ofNat] using
      (RFAP.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero 2 :
        ((2 : Nat) : K) ^ prime = ((2 : Nat) : K))
  have valuePower : value ^ prime = value := by
    unfold value
    exact RFAP.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero
      residue
  have centerPower : center ^ prime = 1 - 2 * value ^ prime := by
    have primeOddPower : Odd prime :=
      primeIsPrime.odd_of_ne_two primeNotTwo
    calc
      center ^ prime = (1 + -(2 * value)) ^ prime := by
        congr 1
        unfold center
        ring1
      _ = 1 ^ prime + (-(2 * value)) ^ prime :=
        RFAP.prime_add_pow prime primeIsPrime primeCastZero oneNonzero 1
          (-(2 * value))
      _ = 1 - (2 * value) ^ prime := by
        rw [one_pow, primeOddPower.neg_pow]
        ring1
      _ = 1 - 2 * value ^ prime := by
        rw [mul_pow, twoPower]
  have centeredEquality :
      1 - 2 * spreadPolynomial prime value = 1 - 2 * value := by
    calc
      1 - 2 * spreadPolynomial prime value =
          spreadBinomialExpansion prime (half + 1) center radialSquare :=
        binomialIdentity
      _ = center ^ prime := expansionCollapse
      _ = 1 - 2 * value ^ prime := centerPower
      _ = 1 - 2 * value := by rw [valuePower]
  have doubledEquality :
      2 * spreadPolynomial prime value = 2 * value := by
    calc
      2 * spreadPolynomial prime value =
          1 - (1 - 2 * spreadPolynomial prime value) := by ring1
      _ = 1 - (1 - 2 * value) := by rw [centeredEquality]
      _ = 2 * value := by ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    spreadPolynomial prime (residue : K) =
        spreadPolynomial prime value := rfl
    _ = (2 * spreadPolynomial prime value) * (2 : K)⁻¹ := by
      calc
        spreadPolynomial prime value =
            spreadPolynomial prime value * 1 := by ring1
        _ = spreadPolynomial prime value * (2 * (2 : K)⁻¹) := by
          rw [twoCancel]
        _ = (2 * spreadPolynomial prime value) * (2 : K)⁻¹ := by ring1
    _ = (2 * value) * (2 : K)⁻¹ := by rw [doubledEquality]
    _ = value := by rw [show (2 * value) * (2 : K)⁻¹ =
      value * (2 * (2 : K)⁻¹) by ring1, twoCancel, mul_one]
    _ = (residue : K) := rfl

end ExerciseEightFive

namespace ExerciseEightEleven

/-- The exact bounded sum occurring in Exercise 8.11.  Natural residues are
cast one at a time; no carrier, root set, or completed family is enumerated. -/
def finiteSpreadInnerProduct
    (primeCardinality firstIndex secondIndex : Nat) : K :=
  RFAP.finitePrefixSum primeCardinality (fun residue =>
    spreadPolynomial firstIndex (residue : K) *
      spreadPolynomial secondIndex (residue : K))

/-- The two exceptional values asked for in Exercise 8.11, in the source's
characteristic-free quotient notation. -/
def lowerExceptionalValue : K := -(1 / 16)

def upperExceptionalValue : K := 1 / 16

/-- The division-free characterizations of the exceptional values. -/
theorem exceptional_values_cleared (sixteenNonzero : (16 : K) ≠ 0) :
    lowerExceptionalValue (K := K) * 16 = -1 ∧
      upperExceptionalValue (K := K) * 16 = 1 := by
  constructor
  · unfold lowerExceptionalValue
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [show -(1 * (16 : K)⁻¹) * 16 =
      -((16 : K) * (16 : K)⁻¹) by ring1]
    rw [RFAP.ExplicitField.mul_inv_cancel 16 sixteenNonzero]
  · unfold upperExceptionalValue
    exact RFAP.ExplicitField.div_mul_cancel 1 sixteenNonzero

end ExerciseEightEleven

namespace ExerciseEightTwelve

/-- The exact finite numerator behind Exercise 8.12.  Under the substitution
`x=1-2s`, the centered spread-polynomial product is the product of the two
Chebyshev values.  This is the algebraic content used before the source invokes
a completed-real weighted integral. -/
theorem exercise_8_12_integrand_cleared
    (firstIndex secondIndex : Nat) (value : K) :
    (2 * spreadPolynomial firstIndex value - 1) *
        (2 * spreadPolynomial secondIndex value - 1) =
      chebyshevFirst firstIndex (1 - 2 * value) *
        chebyshevFirst secondIndex (1 - 2 * value) := by
  rw [exercise_8_4_cleared firstIndex value,
    exercise_8_4_cleared secondIndex value]
  ring1

/-- The same identity in the source's centered `/2` notation. -/
theorem exercise_8_12_integrand
    (firstIndex secondIndex : Nat) (value : K)
    (twoNonzero : (2 : K) ≠ 0) :
    4 *
        (spreadPolynomial firstIndex value - 1 / 2) *
        (spreadPolynomial secondIndex value - 1 / 2) =
      chebyshevFirst firstIndex (1 - 2 * value) *
        chebyshevFirst secondIndex (1 - 2 * value) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have firstCentered :
      2 * (spreadPolynomial firstIndex value - 1 / 2) =
        2 * spreadPolynomial firstIndex value - 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (spreadPolynomial firstIndex value - 1 * (2 : K)⁻¹) =
          2 * spreadPolynomial firstIndex value -
            (2 : K) * (2 : K)⁻¹ := by ring1
      _ = 2 * spreadPolynomial firstIndex value - 1 := by rw [twoCancel]
  have secondCentered :
      2 * (spreadPolynomial secondIndex value - 1 / 2) =
        2 * spreadPolynomial secondIndex value - 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (spreadPolynomial secondIndex value - 1 * (2 : K)⁻¹) =
          2 * spreadPolynomial secondIndex value -
            (2 : K) * (2 : K)⁻¹ := by ring1
      _ = 2 * spreadPolynomial secondIndex value - 1 := by rw [twoCancel]
  calc
    4 * (spreadPolynomial firstIndex value - 1 / 2) *
          (spreadPolynomial secondIndex value - 1 / 2) =
        (2 * (spreadPolynomial firstIndex value - 1 / 2)) *
          (2 * (spreadPolynomial secondIndex value - 1 / 2)) := by ring1
    _ = (2 * spreadPolynomial firstIndex value - 1) *
          (2 * spreadPolynomial secondIndex value - 1) := by
      rw [firstCentered, secondCentered]
    _ = chebyshevFirst firstIndex (1 - 2 * value) *
          chebyshevFirst secondIndex (1 - 2 * value) :=
      exercise_8_12_integrand_cleared firstIndex secondIndex value

end ExerciseEightTwelve

namespace ExerciseEightThirteen

/-- The printed spread-cyclotomic factors.  Each is a literal finite
integer-coefficient expression evaluated in the requested field. -/
def cyclotomicOne (value : K) : K := value
def cyclotomicTwo (value : K) : K := 4 * (1 - value)
def cyclotomicThree (value : K) : K := (3 - 4 * value) ^ 2
def cyclotomicFour (value : K) : K := 4 * (1 - 2 * value) ^ 2
def cyclotomicFive (value : K) : K :=
  (5 - 20 * value + 16 * value ^ 2) ^ 2
def cyclotomicSix (value : K) : K := (1 - 4 * value) ^ 2
def cyclotomicSeven (value : K) : K :=
  (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2
def cyclotomicEight (value : K) : K :=
  4 * (1 - 8 * value + 8 * value ^ 2) ^ 2
def cyclotomicTwelve (value : K) : K :=
  (1 - 16 * value + 16 * value ^ 2) ^ 2

/-- The displayed divisor products through index eight. -/
theorem exercise_8_13_first_eight (value : K) :
    spreadPolynomial 1 value = cyclotomicOne value ∧
      spreadPolynomial 2 value =
        cyclotomicOne value * cyclotomicTwo value ∧
      spreadPolynomial 3 value =
        cyclotomicOne value * cyclotomicThree value ∧
      spreadPolynomial 4 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicFour value ∧
      spreadPolynomial 5 value =
        cyclotomicOne value * cyclotomicFive value ∧
      spreadPolynomial 6 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicThree value * cyclotomicSix value ∧
      spreadPolynomial 7 value =
        cyclotomicOne value * cyclotomicSeven value ∧
      spreadPolynomial 8 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicFour value * cyclotomicEight value := by
  unfold cyclotomicOne cyclotomicTwo cyclotomicThree cyclotomicFour
    cyclotomicFive cyclotomicSix cyclotomicSeven cyclotomicEight
  constructor
  · simp only [spreadPolynomial]
  constructor
  · simp only [spreadPolynomial]
    ring1
  constructor
  · simp only [spreadPolynomial]
    ring1
  constructor
  · simp only [spreadPolynomial]
    ring1
  constructor
  · simp only [spreadPolynomial]
    ring1
  constructor
  · simp only [spreadPolynomial]
    ring1
  constructor
  · simp only [spreadPolynomial]
    ring1
  · simp only [spreadPolynomial]
    ring1

/-- The source's worked `n=12` divisor product. -/
theorem exercise_8_13_twelve (value : K) :
    spreadPolynomial 12 value =
      cyclotomicOne value * cyclotomicTwo value *
        cyclotomicThree value * cyclotomicFour value *
        cyclotomicSix value * cyclotomicTwelve value := by
  unfold cyclotomicOne cyclotomicTwo cyclotomicThree cyclotomicFour
    cyclotomicSix cyclotomicTwelve
  simp only [spreadPolynomial]
  ring1

end ExerciseEightThirteen

end DivineProportions
