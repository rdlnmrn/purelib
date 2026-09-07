import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.TripleCoturn
import mathlib.RFAP.FiniteBinomial
import mathlib.RFAP.QuadraticPair

/-!
# Divine Proportions, Chapter 9: finite turn-rational functions

Exercise 9.3 asks for the rational function obtained after a requested finite
number of equal turn-compositions.  The numerator and denominator are the two
coordinates of `(1 + j u)^n` in the executable pair ring with `j²=-1`.
Consequently every index is a finite power and every general coefficient
formula below is an explicitly bounded binomial prefix.
-/

namespace DivineProportions

/-- The finite pair whose imaginary and real coordinates are respectively the
numerator and denominator of the `n`th turn-rational function. -/
def turnRationalPair
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    RFAP.QuadraticPair R 1 :=
  (⟨1, value⟩ : RFAP.QuadraticPair R 1) ^ index

/-- Numerator of the `n`th turn-rational function. -/
def turnRationalNumerator
    {R : Type*} [CommRing R] (index : Nat) (value : R) : R :=
  (turnRationalPair index value).im

/-- Denominator of the `n`th turn-rational function. -/
def turnRationalDenominator
    {R : Type*} [CommRing R] (index : Nat) (value : R) : R :=
  (turnRationalPair index value).re

/-- The source's rational function `Uₙ`.  Its meaningful quotient statements
below expose the corresponding nonzero denominator. -/
def turnRationalFunction
    {K : Type*} [RFAP.ExplicitField K] (index : Nat) (value : K) : K :=
  turnRationalNumerator index value /
    turnRationalDenominator index value

@[simp] theorem turnRationalNumerator_zero
    {R : Type*} [CommRing R] (value : R) :
    turnRationalNumerator 0 value = 0 := rfl

@[simp] theorem turnRationalDenominator_zero
    {R : Type*} [CommRing R] (value : R) :
    turnRationalDenominator 0 value = 1 := rfl

/-- The numerator update for one additional equal turn. -/
theorem turnRationalNumerator_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    turnRationalNumerator (index + 1) value =
      turnRationalNumerator index value +
        value * turnRationalDenominator index value := by
  unfold turnRationalNumerator turnRationalDenominator turnRationalPair
  rw [pow_succ]
  simp only [RFAP.QuadraticPair.mul_im]
  ring1

/-- The denominator update for one additional equal turn. -/
theorem turnRationalDenominator_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    turnRationalDenominator (index + 1) value =
      turnRationalDenominator index value -
        value * turnRationalNumerator index value := by
  unfold turnRationalNumerator turnRationalDenominator turnRationalPair
  rw [pow_succ]
  simp only [RFAP.QuadraticPair.mul_re]
  ring1

private theorem div_eq_div_of_cross_mul
    {K : Type*} [RFAP.ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        (leftNumerator * leftDenominator⁻¹) *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
      rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- Wherever the two consecutive displayed denominators are nonzero, the
finite rational functions obey the turn-composition rule from Exercise 9.2. -/
theorem turnRationalFunction_succ
    {K : Type*} [RFAP.ExplicitField K]
    (index : Nat) (value : K)
    (currentDenominatorNonzero :
      turnRationalDenominator index value ≠ 0)
    (nextDenominatorNonzero :
      turnRationalDenominator (index + 1) value ≠ 0) :
    turnRationalFunction (index + 1) value =
      turnComposition (turnRationalFunction index value) value := by
  let numerator := turnRationalNumerator index value
  let denominator := turnRationalDenominator index value
  let quotient := numerator / denominator
  have quotientCancel : quotient * denominator = numerator := by
    exact RFAP.ExplicitField.div_mul_cancel numerator
      currentDenominatorNonzero
  have numeratorStep :
      turnRationalNumerator (index + 1) value =
        numerator + value * denominator := by
    exact turnRationalNumerator_succ index value
  have denominatorStep :
      turnRationalDenominator (index + 1) value =
        denominator - value * numerator := by
    exact turnRationalDenominator_succ index value
  have compositionProduct :
      denominator * (1 - quotient * value) =
        turnRationalDenominator (index + 1) value := by
    calc
      denominator * (1 - quotient * value) =
          denominator - value * (quotient * denominator) := by ring1
      _ = denominator - value * numerator := by rw [quotientCancel]
      _ = turnRationalDenominator (index + 1) value :=
        denominatorStep.symm
  have compositionDenominatorNonzero : 1 - quotient * value ≠ 0 := by
    intro zeroComposition
    apply nextDenominatorNonzero
    calc
      turnRationalDenominator (index + 1) value =
          denominator * (1 - quotient * value) := compositionProduct.symm
      _ = 0 := by rw [zeroComposition, mul_zero]
  unfold turnRationalFunction turnComposition
  change
    turnRationalNumerator (index + 1) value /
        turnRationalDenominator (index + 1) value =
      (quotient + value) / (1 - quotient * value)
  apply div_eq_div_of_cross_mul nextDenominatorNonzero
    compositionDenominatorNonzero
  rw [numeratorStep, denominatorStep]
  have quotientDifference : numerator - quotient * denominator = 0 := by
    rw [quotientCancel]
    ring1
  calc
    (numerator + value * denominator) * (1 - quotient * value) =
        (quotient + value) * (denominator - value * numerator) +
          (numerator - quotient * denominator) * (1 + value ^ 2) := by
      ring1
    _ = (quotient + value) * (denominator - value * numerator) := by
      rw [quotientDifference]
      ring1

/-- Primitive recursion for exactly the requested number of equal
turn-compositions. -/
def iteratedTurnComposition
    {K : Type*} [RFAP.ExplicitField K] : Nat → K → K
  | 0, _ => 0
  | index + 1, value =>
      turnComposition (iteratedTurnComposition index value) value

/-- Finite composition meaning of Exercise 9.3.  The premise exposes all and
only the rational-function poles encountered through the requested index. -/
theorem exercise_9_3_finite_iteration
    {K : Type*} [RFAP.ExplicitField K]
    (index : Nat) (value : K)
    (denominatorsNonzero : ∀ current : Nat, current ≤ index →
      turnRationalDenominator current value ≠ 0) :
    iteratedTurnComposition index value =
      turnRationalFunction index value := by
  induction index with
  | zero =>
      unfold iteratedTurnComposition turnRationalFunction
      rw [turnRationalNumerator_zero,
        RFAP.ExplicitField.zero_div]
  | succ index inductionHypothesis =>
      change
        turnComposition (iteratedTurnComposition index value) value =
          turnRationalFunction (index + 1) value
      rw [inductionHypothesis (fun current currentBound =>
        denominatorsNonzero current (by omega0))]
      exact (turnRationalFunction_succ index value
        (denominatorsNonzero index (by omega0))
        (denominatorsNonzero (index + 1) (by omega0))).symm

/-- The numerator and denominator pairs through the fifth requested index. -/
theorem turnRationalPair_first_five
    {R : Type*} [CommRing R] (value : R) :
    (turnRationalNumerator 1 value = value ∧
      turnRationalDenominator 1 value = 1) ∧
    (turnRationalNumerator 2 value = 2 * value ∧
      turnRationalDenominator 2 value = 1 - value ^ 2) ∧
    (turnRationalNumerator 3 value = 3 * value - value ^ 3 ∧
      turnRationalDenominator 3 value = 1 - 3 * value ^ 2) ∧
    (turnRationalNumerator 4 value = 4 * value - 4 * value ^ 3 ∧
      turnRationalDenominator 4 value =
        1 - 6 * value ^ 2 + value ^ 4) ∧
    (turnRationalNumerator 5 value =
        5 * value - 10 * value ^ 3 + value ^ 5 ∧
      turnRationalDenominator 5 value =
        1 - 10 * value ^ 2 + 5 * value ^ 4) := by
  simp only [turnRationalNumerator, turnRationalDenominator,
    turnRationalPair, pow_succ, pow_zero,
    RFAP.QuadraticPair.one_re, RFAP.QuadraticPair.one_im,
    RFAP.QuadraticPair.mul_re, RFAP.QuadraticPair.mul_im]
  constructor
  · constructor <;> ring1
  constructor
  · constructor <;> ring1
  constructor
  · constructor <;> ring1
  constructor <;> constructor <;> ring1

/-- The five rational functions displayed in Exercise 9.3. -/
theorem exercise_9_3_first_five
    {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] (value : K) :
    turnRationalFunction 1 value = value ∧
      turnRationalFunction 2 value =
        (2 * value) / (1 - value ^ 2) ∧
      turnRationalFunction 3 value =
        (3 * value - value ^ 3) / (1 - 3 * value ^ 2) ∧
      turnRationalFunction 4 value =
        (4 * value - 4 * value ^ 3) /
          (1 - 6 * value ^ 2 + value ^ 4) ∧
      turnRationalFunction 5 value =
        (5 * value - 10 * value ^ 3 + value ^ 5) /
          (1 - 10 * value ^ 2 + 5 * value ^ 4) := by
  rcases turnRationalPair_first_five value with
    ⟨⟨numeratorOne, denominatorOne⟩,
      ⟨numeratorTwo, denominatorTwo⟩,
      ⟨numeratorThree, denominatorThree⟩,
      ⟨numeratorFour, denominatorFour⟩,
      numeratorFive, denominatorFive⟩
  unfold turnRationalFunction
  rw [numeratorOne, denominatorOne,
    numeratorTwo, denominatorTwo,
    numeratorThree, denominatorThree,
    numeratorFour, denominatorFour,
    numeratorFive, denominatorFive]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) one_ne_zero
    simpa only [one_mul] using cancel
  simp only [inverseOne, mul_one, true_and]

/-- The `k`th even-binomial term in the general denominator. -/
def turnRationalEvenTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : R :=
  (row.choose (index + index) : R) * (-1) ^ index *
    value ^ (index + index)

/-- The `k`th odd-binomial term in the general numerator. -/
def turnRationalOddTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : R :=
  (row.choose (index + index + 1) : R) * (-1) ^ index *
    value ^ (index + index + 1)

/-- The explicitly bounded alternating even-binomial prefix. -/
def turnRationalEvenExpansion
    {R : Type*} [CommRing R]
    (row half : Nat) (value : R) : R :=
  RFAP.finitePrefixSum (half + 1) (turnRationalEvenTerm row value)

/-- The explicitly bounded alternating odd-binomial prefix. -/
def turnRationalOddExpansion
    {R : Type*} [CommRing R]
    (row half : Nat) (value : R) : R :=
  RFAP.finitePrefixSum (half + 1) (turnRationalOddTerm row value)

private def turnRationalBinomialPairTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : RFAP.QuadraticPair R 1 :=
  (⟨0, value⟩ : RFAP.QuadraticPair R 1) ^ index *
    (row.choose index : RFAP.QuadraticPair R 1)

private theorem pureImaginary_even_power
    {R : Type*} [CommRing R] (value : R) (index : Nat) :
    (⟨0, value⟩ : RFAP.QuadraticPair R 1) ^ (index + index) =
      RFAP.QuadraticPair.scalar
        ((-1 : R) ^ index * value ^ (index + index)) := by
  let generator := RFAP.QuadraticPair.generator (K := R) (radialSquare := 1)
  have pairFactorization :
      (⟨0, value⟩ : RFAP.QuadraticPair R 1) =
        generator * RFAP.QuadraticPair.scalar value := by
    ext <;> simp only [generator, RFAP.QuadraticPair.generator_re,
      RFAP.QuadraticPair.generator_im, RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.mul_re,
      RFAP.QuadraticPair.mul_im]
    all_goals ring1
  rw [pairFactorization, mul_pow,
    RFAP.QuadraticPair.generator_even_power]
  rw [← RFAP.QuadraticPair.scalar_pow,
    ← RFAP.QuadraticPair.scalar_mul]

private theorem pureImaginary_odd_power
    {R : Type*} [CommRing R] (value : R) (index : Nat) :
    (⟨0, value⟩ : RFAP.QuadraticPair R 1) ^
        (index + index + 1) =
      ⟨0, (-1 : R) ^ index * value ^ (index + index + 1)⟩ := by
  rw [pow_succ, pureImaginary_even_power]
  ext
  · simp only [RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.mul_re]
    ring1
  · simp only [RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.mul_im]
    rw [pow_succ]
    ring1

private theorem turnRationalBinomialPairTerm_even
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) :
    turnRationalBinomialPairTerm row value (index + index) =
      RFAP.QuadraticPair.scalar
        (turnRationalEvenTerm row value index) := by
  unfold turnRationalBinomialPairTerm turnRationalEvenTerm
  rw [pureImaginary_even_power,
    RFAP.QuadraticPair.natCast_eq_scalar,
    ← RFAP.QuadraticPair.scalar_mul]
  congr 1
  ring1

private theorem turnRationalBinomialPairTerm_odd
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) :
    turnRationalBinomialPairTerm row value (index + index + 1) =
      ⟨0, turnRationalOddTerm row value index⟩ := by
  unfold turnRationalBinomialPairTerm turnRationalOddTerm
  rw [pureImaginary_odd_power,
    RFAP.QuadraticPair.natCast_eq_scalar]
  ext <;> simp only [RFAP.QuadraticPair.scalar_re,
    RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.mul_re,
    RFAP.QuadraticPair.mul_im]
  all_goals ring1

private theorem finitePrefixSum_quadraticPair_coordinates
    {R : Type*} [CommRing R]
    (count : Nat) (real imaginary : Nat → R) :
    RFAP.finitePrefixSum count (fun index =>
        (⟨real index, imaginary index⟩ : RFAP.QuadraticPair R 1)) =
      ⟨RFAP.finitePrefixSum count real,
        RFAP.finitePrefixSum count imaginary⟩ := by
  induction count generalizing real imaginary with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        ⟨real 0, imaginary 0⟩ +
            RFAP.finitePrefixSum count (fun index =>
              (⟨real (index + 1), imaginary (index + 1)⟩ :
                RFAP.QuadraticPair R 1)) =
          ⟨real 0 + RFAP.finitePrefixSum count
              (fun index => real (index + 1)),
            imaginary 0 + RFAP.finitePrefixSum count
              (fun index => imaginary (index + 1))⟩
      rw [inductionHypothesis]
      rfl

private theorem turnRationalPair_binomial
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    turnRationalPair row value =
      RFAP.finitePrefixSum (row + 1)
        (turnRationalBinomialPairTerm row value) := by
  let offset : RFAP.QuadraticPair R 1 := ⟨0, value⟩
  calc
    turnRationalPair row value = (1 + offset) ^ row := by
      unfold turnRationalPair offset
      congr 1
      ext <;> simp only [RFAP.QuadraticPair.one_re,
        RFAP.QuadraticPair.one_im, RFAP.QuadraticPair.add_re,
        RFAP.QuadraticPair.add_im]
      all_goals ring1
    _ = RFAP.finiteBinomialExpansion row 1 offset :=
      RFAP.finite_binomial_theorem row 1 offset
    _ = RFAP.finitePrefixSum (row + 1)
        (turnRationalBinomialPairTerm row value) := by
      unfold RFAP.finiteBinomialExpansion turnRationalBinomialPairTerm offset
      apply RFAP.finitePrefixSum_congr
      intro index indexBound
      simp only [one_pow, mul_one]

/-- General even-index form requested in Exercise 9.3. -/
theorem turnRationalPair_even_binomial
    {R : Type*} [CommRing R] (half : Nat) (value : R) :
    turnRationalPair (half + half) value =
      ⟨turnRationalEvenExpansion (half + half) half value,
        turnRationalOddExpansion (half + half) half value⟩ := by
  rw [turnRationalPair_binomial]
  rw [RFAP.finitePrefixSum_pairs_and_last]
  have pairedTerms :
      RFAP.finitePrefixSum half (fun index =>
          turnRationalBinomialPairTerm (half + half) value
              (index + index) +
            turnRationalBinomialPairTerm (half + half) value
              (index + index + 1)) =
        RFAP.finitePrefixSum half (fun index =>
          (⟨turnRationalEvenTerm (half + half) value index,
            turnRationalOddTerm (half + half) value index⟩ :
              RFAP.QuadraticPair R 1)) := by
    apply RFAP.finitePrefixSum_congr
    intro index indexBound
    rw [turnRationalBinomialPairTerm_even,
      turnRationalBinomialPairTerm_odd]
    ext <;> simp only [RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.add_re,
      RFAP.QuadraticPair.add_im]
    all_goals ring1
  rw [pairedTerms, finitePrefixSum_quadraticPair_coordinates]
  rw [turnRationalBinomialPairTerm_even]
  have finalOddZero :
      turnRationalOddTerm (half + half) value half = 0 := by
    unfold turnRationalOddTerm
    rw [Nat.choose_succ_self]
    simp only [Nat.cast_zero, zero_mul]
  ext
  · simp only [RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.add_re]
    unfold turnRationalEvenExpansion
    rw [RFAP.finitePrefixSum_succ_last]
  · simp only [RFAP.QuadraticPair.scalar_im,
      RFAP.QuadraticPair.add_im, add_zero]
    unfold turnRationalOddExpansion
    rw [RFAP.finitePrefixSum_succ_last, finalOddZero, add_zero]

/-- General odd-index form requested in Exercise 9.3. -/
theorem turnRationalPair_odd_binomial
    {R : Type*} [CommRing R] (half : Nat) (value : R) :
    turnRationalPair (half + half + 1) value =
      ⟨turnRationalEvenExpansion (half + half + 1) half value,
        turnRationalOddExpansion (half + half + 1) half value⟩ := by
  rw [turnRationalPair_binomial]
  rw [show half + half + 1 + 1 =
    (half + 1) + (half + 1) by omega0]
  rw [RFAP.finitePrefixSum_pairs]
  have pairedTerms :
      RFAP.finitePrefixSum (half + 1) (fun index =>
          turnRationalBinomialPairTerm (half + half + 1) value
              (index + index) +
            turnRationalBinomialPairTerm (half + half + 1) value
              (index + index + 1)) =
        RFAP.finitePrefixSum (half + 1) (fun index =>
          (⟨turnRationalEvenTerm (half + half + 1) value index,
            turnRationalOddTerm (half + half + 1) value index⟩ :
              RFAP.QuadraticPair R 1)) := by
    apply RFAP.finitePrefixSum_congr
    intro index indexBound
    rw [turnRationalBinomialPairTerm_even,
      turnRationalBinomialPairTerm_odd]
    ext <;> simp only [RFAP.QuadraticPair.scalar_re,
      RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.add_re,
      RFAP.QuadraticPair.add_im]
    all_goals ring1
  rw [pairedTerms, finitePrefixSum_quadraticPair_coordinates]
  rfl

/-- The general even-index quotient in Exercise 9.3. -/
theorem exercise_9_3_even
    {K : Type*} [RFAP.ExplicitField K] (half : Nat) (value : K) :
    turnRationalFunction (half + half) value =
      turnRationalOddExpansion (half + half) half value /
        turnRationalEvenExpansion (half + half) half value := by
  unfold turnRationalFunction turnRationalNumerator
    turnRationalDenominator
  rw [turnRationalPair_even_binomial]

/-- The general odd-index quotient in Exercise 9.3. -/
theorem exercise_9_3_odd
    {K : Type*} [RFAP.ExplicitField K] (half : Nat) (value : K) :
    turnRationalFunction (half + half + 1) value =
      turnRationalOddExpansion (half + half + 1) half value /
        turnRationalEvenExpansion (half + half + 1) half value := by
  unfold turnRationalFunction turnRationalNumerator
    turnRationalDenominator
  rw [turnRationalPair_odd_binomial]

end DivineProportions
