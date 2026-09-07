import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.ChapterEightRemaining
import DivineProportions.Trigonometry.PrimeChebyshevSums

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace ExerciseEightEleven

private theorem one_ne_zero_of_two_ne_zero
    (twoNonzero : (2 : K) ≠ 0) : (1 : K) ≠ 0 := by
  intro oneEqualsZero
  apply twoNonzero
  rw [← one_add_one_eq_two, oneEqualsZero, zero_add]

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

private theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

private theorem sixteen_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (16 : K) ≠ 0 := by
  rw [show (16 : K) = (2 * 2) * (2 * 2) by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)

/-- Exercise 8.5 and the centered spread/Chebyshev identity say pointwise
that the `p`th Chebyshev value fixes every centered natural residue label. -/
theorem chebyshevFirst_prime_centered_residue
    (prime residue : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    chebyshevFirst prime (1 - 2 * (residue : K)) =
      1 - 2 * (residue : K) := by
  have fixed := ExerciseEightFive.exercise_8_5_prime_residue
    (K := K) prime residue primeIsPrime primeCastZero twoNonzero
  have centered := exercise_8_4_cleared prime (residue : K)
  rw [fixed] at centered
  calc
    chebyshevFirst prime (1 - 2 * (residue : K)) =
        1 - (1 - chebyshevFirst prime (1 - 2 * (residue : K))) := by
          ring1
    _ = 1 - 2 * (residue : K) := by rw [← centered]

/-- Consequently the bounded sum at index `p` is the already-vanishing sum
at index one. -/
theorem prime_centered_chebyshev_sum_prime_zero
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    finiteCenteredChebyshevSum (K := K) prime prime = 0 := by
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have oneBelow : 1 < prime - 1 := by
    have twoAtMost := primeIsPrime.two_le
    omega0
  rw [finiteCenteredChebyshevSum_eq_prefix]
  calc
    RFAP.finitePrefixSum prime (fun residue =>
        chebyshevFirst prime (1 - 2 * (residue : K))) =
      RFAP.finitePrefixSum prime (fun residue =>
        chebyshevFirst 1 (1 - 2 * (residue : K))) := by
          apply RFAP.finitePrefixSum_congr
          intro residue residueBelow
          rw [chebyshevFirst_prime_centered_residue prime residue
            primeIsPrime primeCastZero twoNonzero,
            chebyshevFirst_one]
    _ = finiteCenteredChebyshevSum (K := K) prime 1 :=
      (finiteCenteredChebyshevSum_eq_prefix prime 1).symm
    _ = 0 := prime_centered_chebyshev_sum_zero prime primeIsPrime
      primeCastZero oneNonzero 1 oneBelow

/-- Frobenius at the centered labels reflects Chebyshev sums across index
`p`: `A_(p+t)+A_(p-t)=A_(t+1)+A_(t-1)`. -/
theorem prime_centered_chebyshev_sum_reflection
    (prime step : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (stepPositive : 1 ≤ step) (stepAtMostPrime : step ≤ prime) :
    finiteCenteredChebyshevSum (K := K) prime (prime + step) +
        finiteCenteredChebyshevSum prime (prime - step) =
      finiteCenteredChebyshevSum prime (step + 1) +
        finiteCenteredChebyshevSum prime (step - 1) := by
  let center : Nat → K := fun residue => 1 - 2 * (residue : K)
  let upperProduct := RFAP.finitePrefixSum prime (fun residue =>
    chebyshevFirst step (center residue) *
      chebyshevFirst prime (center residue))
  let lowerProduct := RFAP.finitePrefixSum prime (fun residue =>
    chebyshevFirst 1 (center residue) *
      chebyshevFirst step (center residue))
  have productsEqual : upperProduct = lowerProduct := by
    unfold upperProduct lowerProduct
    apply RFAP.finitePrefixSum_congr
    intro residue residueBelow
    rw [chebyshevFirst_prime_centered_residue prime residue primeIsPrime
      primeCastZero twoNonzero, chebyshevFirst_one]
    ring1
  have upper := finiteCenteredChebyshev_product_sum
    (K := K) prime step prime stepAtMostPrime
  have lower := finiteCenteredChebyshev_product_sum
    (K := K) prime 1 step stepPositive
  change 2 * upperProduct = _ at upper
  change 2 * lowerProduct = _ at lower
  calc
    finiteCenteredChebyshevSum (K := K) prime (prime + step) +
        finiteCenteredChebyshevSum prime (prime - step) =
      2 * upperProduct := by
        rw [upper]
        rw [Nat.add_comm]
    _ = 2 * lowerProduct := by rw [productsEqual]
    _ = finiteCenteredChebyshevSum prime (1 + step) +
        finiteCenteredChebyshevSum prime (step - 1) := lower
    _ = finiteCenteredChebyshevSum prime (step + 1) +
        finiteCenteredChebyshevSum prime (step - 1) := by
          rw [Nat.add_comm]

/-- All reflected sums strictly beyond the upper exceptional index and still
within the Exercise 8.11 range vanish. -/
theorem prime_centered_chebyshev_sum_high_zero
    (prime step : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (twoAtMostStep : 2 ≤ step) (stepAtMost : step ≤ prime - 4) :
    finiteCenteredChebyshevSum (K := K) prime (prime + step) = 0 := by
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  have reflection := prime_centered_chebyshev_sum_reflection
    (K := K) prime step primeIsPrime primeCastZero twoNonzero
      (by omega0) (by omega0)
  rw [prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (prime - step) (by omega0),
    prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (step + 1) (by omega0),
    prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (step - 1) (by omega0),
    add_zero, zero_add] at reflection
  exact reflection

/-- The upper exceptional Chebyshev sum has the opposite cleared value from
the Fermat-boundary sum. -/
theorem prime_centered_chebyshev_sum_upper_boundary_cleared
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (fourBelowPrime : 4 < prime) :
    2 * finiteCenteredChebyshevSum (K := K) prime (prime + 1) = 1 := by
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  have reflection := prime_centered_chebyshev_sum_reflection
    (K := K) prime 1 primeIsPrime primeCastZero twoNonzero
      (by omega0) (by omega0)
  rw [show prime - 1 = prime - 1 by rfl,
    prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero 2 (by omega0),
    prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero 0 (by omega0),
    add_zero] at reflection
  have lowerBoundary := prime_centered_chebyshev_sum_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero oneNonzero twoNonzero
  calc
    2 * finiteCenteredChebyshevSum (K := K) prime (prime + 1) =
        -(2 * finiteCenteredChebyshevSum prime (prime - 1)) := by
          rw [show finiteCenteredChebyshevSum (K := K) prime (prime + 1) =
              -finiteCenteredChebyshevSum prime (prime - 1) by
                exact eq_neg_of_add_eq_zero_left reflection]
          ring1
    _ = 1 := by rw [lowerBoundary]; ring1

/-- Complete zero classification for the sum indices that can occur in
Exercise 8.11, excluding its two displayed exceptional indices. -/
theorem prime_centered_chebyshev_sum_regular_zero
    (prime index : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (indexAtMost : index ≤ prime + prime - 4)
    (notLowerBoundary : index ≠ prime - 1)
    (notUpperBoundary : index ≠ prime + 1) :
    finiteCenteredChebyshevSum (K := K) prime index = 0 := by
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  by_cases belowBoundary : index < prime - 1
  · exact prime_centered_chebyshev_sum_zero prime primeIsPrime
      primeCastZero oneNonzero index belowBoundary
  · by_cases indexAtMostPrime : index ≤ prime
    · have indexEqualsPrime : index = prime := by omega0
      subst index
      exact prime_centered_chebyshev_sum_prime_zero prime primeIsPrime
        primeCastZero twoNonzero
    · let step := index - prime
      have indexEquation : index = prime + step := by
        unfold step
        omega0
      have twoAtMostStep : 2 ≤ step := by
        unfold step
        omega0
      have stepAtMost : step ≤ prime - 4 := by
        unfold step
        omega0
      rw [indexEquation]
      exact prime_centered_chebyshev_sum_high_zero prime step primeIsPrime
        primeCastZero twoNonzero twoAtMostStep stepAtMost

/-- The bounded spread inner product is symmetric in its two indices. -/
theorem finiteSpreadInnerProduct_comm
    (prime first second : Nat) :
    finiteSpreadInnerProduct (K := K) prime first second =
      finiteSpreadInnerProduct prime second first := by
  unfold finiteSpreadInnerProduct
  apply RFAP.finitePrefixSum_congr
  intro residue residueBelow
  ring1

/-- After clearing the two centered-spread factors and the Chebyshev
product-to-sum factor, the inner product is exactly the Chebyshev sum at the
sum of the indices. -/
theorem finiteSpreadInnerProduct_chebyshev_cleared_of_le
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstAtMostSecond : first ≤ second)
    (firstBelow : first < prime - 1) (secondBelow : second < prime - 1) :
    8 * finiteSpreadInnerProduct (K := K) prime first second =
      finiteCenteredChebyshevSum prime (first + second) := by
  let center : Nat → K := fun residue => 1 - 2 * (residue : K)
  let productSum := RFAP.finitePrefixSum prime (fun residue =>
    chebyshevFirst first (center residue) *
      chebyshevFirst second (center residue))
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  have pointwise (residue : Nat) :
      4 * (spreadPolynomial first (residue : K) *
          spreadPolynomial second (residue : K)) =
        1 - chebyshevFirst first (center residue) -
            chebyshevFirst second (center residue) +
          chebyshevFirst first (center residue) *
            chebyshevFirst second (center residue) := by
    have firstCentered := exercise_8_4_cleared first (residue : K)
    have secondCentered := exercise_8_4_cleared second (residue : K)
    change 2 * spreadPolynomial first (residue : K) =
      1 - chebyshevFirst first (center residue) at firstCentered
    change 2 * spreadPolynomial second (residue : K) =
      1 - chebyshevFirst second (center residue) at secondCentered
    rw [show 4 * (spreadPolynomial first (residue : K) *
          spreadPolynomial second (residue : K)) =
        (2 * spreadPolynomial first (residue : K)) *
          (2 * spreadPolynomial second (residue : K)) by ring1,
      firstCentered, secondCentered]
    ring1
  have fourTimesInner :
      4 * finiteSpreadInnerProduct (K := K) prime first second =
        productSum := by
    unfold finiteSpreadInnerProduct
    rw [show 4 * RFAP.finitePrefixSum prime (fun residue =>
          spreadPolynomial first (residue : K) *
            spreadPolynomial second (residue : K)) =
        RFAP.finitePrefixSum prime (fun residue =>
          4 * (spreadPolynomial first (residue : K) *
            spreadPolynomial second (residue : K))) by
          exact (RFAP.finitePrefixSum_mul_left prime 4 _).symm]
    calc
      RFAP.finitePrefixSum prime (fun residue =>
          4 * (spreadPolynomial first (residue : K) *
            spreadPolynomial second (residue : K))) =
        RFAP.finitePrefixSum prime (fun residue =>
          1 - chebyshevFirst first (center residue) -
              chebyshevFirst second (center residue) +
            chebyshevFirst first (center residue) *
              chebyshevFirst second (center residue)) := by
                apply RFAP.finitePrefixSum_congr
                intro residue residueBelow
                exact pointwise residue
      _ = RFAP.finitePrefixSum prime (fun _ : Nat => (1 : K)) -
            RFAP.finitePrefixSum prime (fun residue =>
              chebyshevFirst first (center residue)) -
            RFAP.finitePrefixSum prime (fun residue =>
              chebyshevFirst second (center residue)) +
          productSum := by
            unfold productSum
            rw [RFAP.finitePrefixSum_add,
              RFAP.finitePrefixSum_sub, RFAP.finitePrefixSum_sub]
      _ = (prime : K) -
            finiteCenteredChebyshevSum prime first -
            finiteCenteredChebyshevSum prime second + productSum := by
              rw [RFAP.finitePrefixSum_one,
                ← finiteCenteredChebyshevSum_eq_prefix,
                ← finiteCenteredChebyshevSum_eq_prefix]
      _ = productSum := by
        rw [primeCastZero,
          prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
            oneNonzero first firstBelow,
          prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
            oneNonzero second secondBelow]
        ring1
  have productToSum := finiteCenteredChebyshev_product_sum
    (K := K) prime first second firstAtMostSecond
  change 2 * productSum = _ at productToSum
  have differenceBelow : second - first < prime - 1 := by omega0
  have differenceZero := prime_centered_chebyshev_sum_zero
    (K := K) prime primeIsPrime primeCastZero oneNonzero
      (second - first) differenceBelow
  calc
    8 * finiteSpreadInnerProduct (K := K) prime first second =
        2 * (4 * finiteSpreadInnerProduct prime first second) := by ring1
    _ = 2 * productSum := by rw [fourTimesInner]
    _ = finiteCenteredChebyshevSum prime (first + second) +
        finiteCenteredChebyshevSum prime (second - first) := productToSum
    _ = finiteCenteredChebyshevSum prime (first + second) := by
      rw [differenceZero, add_zero]

/-- Symmetric version of the cleared inner-product identity. -/
theorem finiteSpreadInnerProduct_chebyshev_cleared
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstBelow : first < prime - 1) (secondBelow : second < prime - 1) :
    8 * finiteSpreadInnerProduct (K := K) prime first second =
      finiteCenteredChebyshevSum prime (first + second) := by
  by_cases firstAtMostSecond : first ≤ second
  · exact finiteSpreadInnerProduct_chebyshev_cleared_of_le
      prime first second primeIsPrime primeCastZero twoNonzero
        firstAtMostSecond firstBelow secondBelow
  · have secondAtMostFirst : second ≤ first := by omega0
    have reversed := finiteSpreadInnerProduct_chebyshev_cleared_of_le
      (K := K) prime second first primeIsPrime primeCastZero twoNonzero
        secondAtMostFirst secondBelow firstBelow
    rw [← finiteSpreadInnerProduct_comm prime first second,
      Nat.add_comm] at reversed
    exact reversed

/-- The ordinary case of Exercise 8.11: throughout the requested finite
index box, the bounded inner product vanishes away from the two exceptional
index sums. -/
theorem finiteSpreadInnerProduct_zero
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2)
    (notLowerExceptional : first + second ≠ prime - 1)
    (notUpperExceptional : first + second ≠ prime + 1) :
    finiteSpreadInnerProduct (K := K) prime first second = 0 := by
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have cleared := finiteSpreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  have chebyshevZero := prime_centered_chebyshev_sum_regular_zero
    (K := K) prime (first + second) primeIsPrime primeCastZero twoNonzero
      (by omega0) notLowerExceptional notUpperExceptional
  apply eq_zero_of_mul_eq_zero_left (eight_ne_zero twoNonzero)
  rw [cleared, chebyshevZero]

/-- At `m+n=p-1`, the exact exceptional value is `-1/16`. -/
theorem finiteSpreadInnerProduct_lower_exceptional
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (_firstAtMost : first ≤ prime - 2)
    (_secondAtMost : second ≤ prime - 2)
    (sumEquation : first + second = prime - 1) :
    finiteSpreadInnerProduct (K := K) prime first second =
      lowerExceptionalValue := by
  have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have innerCleared := finiteSpreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  rw [sumEquation] at innerCleared
  have boundary := prime_centered_chebyshev_sum_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero oneNonzero twoNonzero
  have sixteenTimesInner :
      16 * finiteSpreadInnerProduct (K := K) prime first second = -1 := by
    calc
      16 * finiteSpreadInnerProduct (K := K) prime first second =
          2 * (8 * finiteSpreadInnerProduct prime first second) := by ring1
      _ = 2 * finiteCenteredChebyshevSum prime (prime - 1) := by
        rw [innerCleared]
      _ = -1 := boundary
  have exceptional :=
    (exceptional_values_cleared (K := K) (sixteen_ne_zero twoNonzero)).1
  apply eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * finiteSpreadInnerProduct (K := K) prime first second = -1 :=
      sixteenTimesInner
    _ = 16 * lowerExceptionalValue (K := K) := by
      rw [show 16 * lowerExceptionalValue (K := K) =
          lowerExceptionalValue * 16 by ring1, exceptional]

/-- At `m+n=p+1`, the exact exceptional value is `1/16`. -/
theorem finiteSpreadInnerProduct_upper_exceptional
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2)
    (sumEquation : first + second = prime + 1) :
    finiteSpreadInnerProduct (K := K) prime first second =
      upperExceptionalValue := by
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have fourBelowPrime : 4 < prime := by omega0
  have innerCleared := finiteSpreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  rw [sumEquation] at innerCleared
  have boundary := prime_centered_chebyshev_sum_upper_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero twoNonzero fourBelowPrime
  have sixteenTimesInner :
      16 * finiteSpreadInnerProduct (K := K) prime first second = 1 := by
    calc
      16 * finiteSpreadInnerProduct (K := K) prime first second =
          2 * (8 * finiteSpreadInnerProduct prime first second) := by ring1
      _ = 2 * finiteCenteredChebyshevSum prime (prime + 1) := by
        rw [innerCleared]
      _ = 1 := boundary
  have exceptional :=
    (exceptional_values_cleared (K := K) (sixteen_ne_zero twoNonzero)).2
  apply eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * finiteSpreadInnerProduct (K := K) prime first second = 1 :=
      sixteenTimesInner
    _ = 16 * upperExceptionalValue (K := K) := by
      rw [show 16 * upperExceptionalValue (K := K) =
          upperExceptionalValue * 16 by ring1, exceptional]

/-- Exercise 8.11 in one finite statement: all requested bounded inner
products vanish except at index sums `p-1` and `p+1`, where their values are
respectively `-1/16` and `1/16`. -/
theorem exercise_8_11
    (prime first second : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2) :
    ((first + second ≠ prime - 1 ∧ first + second ≠ prime + 1) →
        finiteSpreadInnerProduct (K := K) prime first second = 0) ∧
      (first + second = prime - 1 →
        finiteSpreadInnerProduct (K := K) prime first second =
          lowerExceptionalValue) ∧
      (first + second = prime + 1 →
        finiteSpreadInnerProduct (K := K) prime first second =
          upperExceptionalValue) := by
  constructor
  · intro regular
    exact finiteSpreadInnerProduct_zero prime first second primeIsPrime
      primeCastZero twoNonzero firstPositive secondPositive firstAtMost
        secondAtMost regular.1 regular.2
  · constructor
    · intro lower
      exact finiteSpreadInnerProduct_lower_exceptional prime first second
        primeIsPrime primeCastZero twoNonzero firstPositive secondPositive
          firstAtMost secondAtMost lower
    · intro upper
      exact finiteSpreadInnerProduct_upper_exceptional prime first second
        primeIsPrime primeCastZero twoNonzero firstPositive secondPositive
          firstAtMost secondAtMost upper

end ExerciseEightEleven

end DivineProportions
