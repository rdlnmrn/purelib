import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadBinomial

/-!
# Divine Proportions, Chapter 8: odd spread-polynomial squares

Exercise 8.7 is proved in two nested executable quadratic-pair rings.  They
adjoin only the two formal relations needed by the finite binomial argument;
no root is selected in the coefficient field.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The `k`th term inside the square in Exercise 8.7. -/
def oddSpreadRootTerm
    (half : Nat) (value : K) (index : Nat) : K :=
  (-value) ^ index * (1 - value) ^ (half - index) *
    ((half + half + 1).choose (index + index + 1) : K)

/-- The explicitly bounded polynomial inside Exercise 8.7's square. -/
def oddSpreadRootExpansion (half : Nat) (value : K) : K :=
  RFAP.finitePrefixSum (half + 1) (oddSpreadRootTerm half value)

/-- The last displayed term is exactly `(-s)^l`. -/
theorem oddSpreadRootTerm_last (half : Nat) (value : K) :
    oddSpreadRootTerm half value half = (-value) ^ half := by
  unfold oddSpreadRootTerm
  rw [Nat.sub_self,
    show half + half + 1 = half + half + 1 by rfl,
    RFAP.finite_choose_self, pow_zero, Nat.cast_one]
  ring1

/-- Primitive-recursive spread polynomials commute with the scalar embedding
into a finite quadratic-pair ring. -/
theorem spreadPolynomial_quadraticPair_scalar
    {R : Type*} [CommRing R]
    (radialSquare value : R) (index : Nat) :
    spreadPolynomial index
        (RFAP.QuadraticPair.scalar (radialSquare := radialSquare) value) =
      RFAP.QuadraticPair.scalar
        (spreadPolynomial index value) := by
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          simp only [spreadPolynomial_zero,
            RFAP.QuadraticPair.scalar_zero]
      | succ index =>
          cases index with
          | zero =>
              rfl
          | succ index =>
              change
                spreadPolynomial (index + 2)
                    (RFAP.QuadraticPair.scalar value) =
                  RFAP.QuadraticPair.scalar
                    (spreadPolynomial (index + 2) value)
              rw [spreadPolynomial_succ_succ,
                spreadPolynomial_succ_succ]
              rw [inductionHypothesis (index + 1) (by omega0),
                inductionHypothesis index (by omega0)]
              rw [RFAP.QuadraticPair.two_eq_scalar]
              apply RFAP.QuadraticPair.ext <;>
                simp only [RFAP.QuadraticPair.mul_re,
                  RFAP.QuadraticPair.mul_im,
                  RFAP.QuadraticPair.add_re,
                  RFAP.QuadraticPair.add_im,
                  RFAP.QuadraticPair.sub_re,
                  RFAP.QuadraticPair.sub_im,
                  RFAP.QuadraticPair.scalar_re,
                  RFAP.QuadraticPair.scalar_im,
                  RFAP.QuadraticPair.one_re,
                  RFAP.QuadraticPair.one_im]
              all_goals ring1

namespace ExerciseEightSeven

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

private theorem innerGenerator_even_power
    (value : K) (index : Nat) :
    let generator :=
      RFAP.QuadraticPair.generator (K := K)
        (radialSquare := value - 1)
    generator ^ (index + index) =
      RFAP.QuadraticPair.scalar
        (radialSquare := value - 1) ((1 - value) ^ index) := by
  dsimp only
  calc
    RFAP.QuadraticPair.generator (K := K)
          (radialSquare := value - 1) ^ (index + index) =
        RFAP.QuadraticPair.scalar ((-(value - 1)) ^ index) :=
      RFAP.QuadraticPair.generator_even_power index
    _ = RFAP.QuadraticPair.scalar ((1 - value) ^ index) := by
      congr 1
      congr 1
      ring1

private theorem antisymmetricTerm_nested
    (half index : Nat) (value : K) (indexBound : index < half + 1) :
    let innerScalar :=
      RFAP.QuadraticPair.scalar (radialSquare := value - 1)
    let innerGenerator :=
      RFAP.QuadraticPair.generator (K := K)
        (radialSquare := value - 1)
    let outerScalar :=
      RFAP.QuadraticPair.scalar
        (radialSquare := innerScalar value)
    let outerGenerator :=
      RFAP.QuadraticPair.generator
        (K := RFAP.QuadraticPair K (value - 1))
        (radialSquare := innerScalar value)
    outerGenerator ^ (index + index) *
          (outerScalar innerGenerator) ^
            (half + half + 1 - (index + index + 1)) *
        ((half + half + 1).choose (index + index + 1) :
          RFAP.QuadraticPair
            (RFAP.QuadraticPair K (value - 1)) (innerScalar value)) =
      outerScalar (innerScalar (oddSpreadRootTerm half value index)) := by
  dsimp only
  let innerScalar :=
    RFAP.QuadraticPair.scalar (radialSquare := value - 1)
  let innerGenerator :=
    RFAP.QuadraticPair.generator (K := K)
      (radialSquare := value - 1)
  let outerScalar :=
    RFAP.QuadraticPair.scalar (radialSquare := innerScalar value)
  let outerGenerator :=
    RFAP.QuadraticPair.generator
      (K := RFAP.QuadraticPair K (value - 1))
      (radialSquare := innerScalar value)
  have outerEvenPower :
      outerGenerator ^ (index + index) =
        outerScalar (innerScalar ((-value) ^ index)) := by
    calc
      outerGenerator ^ (index + index) =
          outerScalar ((-innerScalar value) ^ index) :=
        RFAP.QuadraticPair.generator_even_power index
      _ = outerScalar (innerScalar ((-value) ^ index)) := by
        rw [← RFAP.QuadraticPair.scalar_neg,
          ← RFAP.QuadraticPair.scalar_pow]
  have exponentEquation :
      half + half + 1 - (index + index + 1) =
        (half - index) + (half - index) := by omega0
  have centerPower :
      (outerScalar innerGenerator) ^
          (half + half + 1 - (index + index + 1)) =
        outerScalar (innerScalar ((1 - value) ^ (half - index))) := by
    rw [exponentEquation]
    rw [← RFAP.QuadraticPair.scalar_pow]
    rw [innerGenerator_even_power]
  have coefficientCast :
      ((half + half + 1).choose (index + index + 1) :
          RFAP.QuadraticPair
            (RFAP.QuadraticPair K (value - 1)) (innerScalar value)) =
        outerScalar (innerScalar
          ((half + half + 1).choose (index + index + 1) : K)) := by
    rw [RFAP.QuadraticPair.natCast_eq_scalar,
      RFAP.QuadraticPair.natCast_eq_scalar]
  rw [outerEvenPower, centerPower, coefficientCast]
  unfold oddSpreadRootTerm
  rw [← RFAP.QuadraticPair.scalar_mul,
    ← RFAP.QuadraticPair.scalar_mul]
  congr 1
  rw [← RFAP.QuadraticPair.scalar_mul,
    ← RFAP.QuadraticPair.scalar_mul]

/-- Exercise 8.7: for every odd requested index `n=2l+1`, the spread
polynomial is `s` times the square of the source's finite odd-binomial
polynomial. -/
theorem exercise_8_7
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    spreadPolynomial (half + half + 1) value =
      value * oddSpreadRootExpansion half value ^ 2 := by
  let innerScalar :=
    RFAP.QuadraticPair.scalar (radialSquare := value - 1)
  let innerGenerator :=
    RFAP.QuadraticPair.generator (K := K)
      (radialSquare := value - 1)
  let outerScalar :=
    RFAP.QuadraticPair.scalar (radialSquare := innerScalar value)
  let outerGenerator :=
    RFAP.QuadraticPair.generator
      (K := RFAP.QuadraticPair K (value - 1))
      (radialSquare := innerScalar value)
  let embeddedValue := outerScalar (innerScalar value)
  let embeddedRoot :=
    outerScalar (innerScalar (oddSpreadRootExpansion half value))
  let positive := outerScalar innerGenerator + outerGenerator
  let negative := outerScalar innerGenerator - outerGenerator
  let offset := 2 * outerScalar innerGenerator * outerGenerator
  have innerSquare : innerGenerator ^ 2 = innerScalar (1 - value) := by
    unfold innerGenerator innerScalar
    calc
      RFAP.QuadraticPair.generator (K := K)
            (radialSquare := value - 1) ^ 2 =
          RFAP.QuadraticPair.scalar ((1 - value) ^ 1) := by
            simpa only [show 1 + 1 = 2 by omega0] using
              innerGenerator_even_power value 1
      _ = RFAP.QuadraticPair.scalar (1 - value) := by rw [pow_one]
  have outerSquare : outerGenerator ^ 2 = -embeddedValue := by
    unfold outerGenerator embeddedValue outerScalar
    calc
      RFAP.QuadraticPair.generator
            (K := RFAP.QuadraticPair K (value - 1))
            (radialSquare := innerScalar value) ^ 2 =
          outerScalar (-innerScalar value) :=
        RFAP.QuadraticPair.generator_square
      _ = -outerScalar (innerScalar value) := by
        exact RFAP.QuadraticPair.scalar_neg (innerScalar value)
  have embeddedInnerSquare :
      (outerScalar innerGenerator) ^ 2 = 1 - embeddedValue := by
    rw [← RFAP.QuadraticPair.scalar_pow, innerSquare]
    unfold embeddedValue
    rw [← RFAP.QuadraticPair.scalar_one,
      ← RFAP.QuadraticPair.scalar_one,
      ← RFAP.QuadraticPair.scalar_sub,
      ← RFAP.QuadraticPair.scalar_sub]
  have positiveNegative : positive * negative = 1 := by
    unfold positive negative
    calc
      (outerScalar innerGenerator + outerGenerator) *
          (outerScalar innerGenerator - outerGenerator) =
        (outerScalar innerGenerator) ^ 2 - outerGenerator ^ 2 := by ring1
      _ = (1 - embeddedValue) - (-embeddedValue) := by
        rw [embeddedInnerSquare, outerSquare]
      _ = 1 := by ring1
  have powerProduct :
      positive ^ (half + half + 1) *
          negative ^ (half + half + 1) = 1 := by
    rw [← mul_pow, positiveNegative, one_pow]
  have antisymmetricRaw := antisymmetric_binomial_odd half
    (outerScalar innerGenerator) outerGenerator
  have antisymmetricTerms :
      RFAP.finitePrefixSum (half + 1) (fun index =>
          outerGenerator ^ (index + index) *
            (outerScalar innerGenerator) ^
              (half + half + 1 - (index + index + 1)) *
              ((half + half + 1).choose (index + index + 1) :
                RFAP.QuadraticPair
                  (RFAP.QuadraticPair K (value - 1))
                  (innerScalar value))) = embeddedRoot := by
    unfold embeddedRoot oddSpreadRootExpansion
    calc
      RFAP.finitePrefixSum (half + 1) (fun index =>
          outerGenerator ^ (index + index) *
            (outerScalar innerGenerator) ^
              (half + half + 1 - (index + index + 1)) *
              ((half + half + 1).choose (index + index + 1) :
                RFAP.QuadraticPair
                  (RFAP.QuadraticPair K (value - 1))
                  (innerScalar value))) =
        RFAP.finitePrefixSum (half + 1) (fun index =>
          outerScalar (innerScalar (oddSpreadRootTerm half value index))) := by
            apply RFAP.finitePrefixSum_congr
            intro index indexBound
            exact antisymmetricTerm_nested half index value indexBound
      _ = outerScalar (RFAP.finitePrefixSum (half + 1) (fun index =>
          innerScalar (oddSpreadRootTerm half value index))) :=
        finitePrefixSum_quadraticPair_scalar
          (innerScalar value) (half + 1) _
      _ = outerScalar (innerScalar (RFAP.finitePrefixSum (half + 1)
          (oddSpreadRootTerm half value))) := by
            rw [finitePrefixSum_quadraticPair_scalar]
  have antisymmetric :
      positive ^ (half + half + 1) -
          negative ^ (half + half + 1) =
        2 * outerGenerator * embeddedRoot := by
    unfold positive negative
    rw [antisymmetricTerms] at antisymmetricRaw
    exact antisymmetricRaw
  have offsetSquare :
      offset ^ 2 = -(4 * embeddedValue * (1 - embeddedValue)) := by
    unfold offset
    calc
      (2 * outerScalar innerGenerator * outerGenerator) ^ 2 =
          4 * (outerScalar innerGenerator) ^ 2 *
            outerGenerator ^ 2 := by ring1
      _ = 4 * (1 - embeddedValue) * (-embeddedValue) := by
        rw [embeddedInnerSquare, outerSquare]
      _ = -(4 * embeddedValue * (1 - embeddedValue)) := by ring1
  have positiveSquare :
      positive ^ 2 = 1 - 2 * embeddedValue + offset := by
    unfold positive offset
    rw [add_sq]
    rw [embeddedInnerSquare, outerSquare]
    ring1
  have negativeSquare :
      negative ^ 2 = 1 - 2 * embeddedValue - offset := by
    unfold negative offset
    rw [sub_sq]
    rw [embeddedInnerSquare, outerSquare]
    ring1
  have positiveEvenPower :
      (1 - 2 * embeddedValue + offset) ^ (half + half + 1) =
        positive ^ ((half + half + 1) + (half + half + 1)) := by
    rw [← positiveSquare, ← pow_mul]
    congr 1
    omega0
  have negativeEvenPower :
      (1 - 2 * embeddedValue - offset) ^ (half + half + 1) =
        negative ^ ((half + half + 1) + (half + half + 1)) := by
    rw [← negativeSquare, ← pow_mul]
    congr 1
    omega0
  have embeddedSpread :
      spreadPolynomial (half + half + 1) embeddedValue =
        outerScalar (innerScalar
          (spreadPolynomial (half + half + 1) value)) := by
    unfold embeddedValue
    rw [spreadPolynomial_quadraticPair_scalar,
      spreadPolynomial_quadraticPair_scalar]
  have spreadFormula := spread_polynomial_offset_formula_cleared
    embeddedValue offset offsetSquare (half + half + 1)
  rw [positiveEvenPower, negativeEvenPower, embeddedSpread] at spreadFormula
  have positivePowerSquare :
      (positive ^ (half + half + 1)) ^ 2 =
        positive ^ ((half + half + 1) + (half + half + 1)) := by
    rw [pow_two, ← pow_add]
  have negativePowerSquare :
      (negative ^ (half + half + 1)) ^ 2 =
        negative ^ ((half + half + 1) + (half + half + 1)) := by
    rw [pow_two, ← pow_add]
  have embeddedEquation :
      4 * outerScalar (innerScalar
          (spreadPolynomial (half + half + 1) value)) =
        4 * embeddedValue * embeddedRoot ^ 2 := by
    calc
      4 * outerScalar (innerScalar
          (spreadPolynomial (half + half + 1) value)) =
        2 - positive ^ ((half + half + 1) + (half + half + 1)) -
          negative ^ ((half + half + 1) + (half + half + 1)) :=
            spreadFormula
      _ = -(positive ^ (half + half + 1) -
          negative ^ (half + half + 1)) ^ 2 := by
            rw [← positivePowerSquare, ← negativePowerSquare]
            calc
              2 - (positive ^ (half + half + 1)) ^ 2 -
                    (negative ^ (half + half + 1)) ^ 2 =
                  2 * (positive ^ (half + half + 1) *
                      negative ^ (half + half + 1)) -
                    (positive ^ (half + half + 1)) ^ 2 -
                    (negative ^ (half + half + 1)) ^ 2 := by
                      rw [powerProduct]
                      ring1
              _ = -(positive ^ (half + half + 1) -
                  negative ^ (half + half + 1)) ^ 2 := by ring1
      _ = -(2 * outerGenerator * embeddedRoot) ^ 2 := by
            rw [antisymmetric]
      _ = 4 * embeddedValue * embeddedRoot ^ 2 := by
            calc
              -(2 * outerGenerator * embeddedRoot) ^ 2 =
                  -4 * outerGenerator ^ 2 * embeddedRoot ^ 2 := by ring1
              _ = 4 * embeddedValue * embeddedRoot ^ 2 := by
                rw [outerSquare]
                ring1
  have embeddedRootSquare :
      embeddedRoot ^ 2 = outerScalar (innerScalar
        (oddSpreadRootExpansion half value ^ 2)) := by
    unfold embeddedRoot
    rw [← RFAP.QuadraticPair.scalar_pow,
      ← RFAP.QuadraticPair.scalar_pow]
  rw [embeddedRootSquare] at embeddedEquation
  rw [RFAP.QuadraticPair.four_eq_scalar] at embeddedEquation
  rw [← RFAP.QuadraticPair.scalar_mul,
    ← RFAP.QuadraticPair.scalar_mul] at embeddedEquation
  have innerEquation := congrArg RFAP.QuadraticPair.re embeddedEquation
  simp only [RFAP.QuadraticPair.scalar_re] at innerEquation
  rw [RFAP.QuadraticPair.four_eq_scalar] at innerEquation
  rw [← RFAP.QuadraticPair.scalar_mul,
    ← RFAP.QuadraticPair.scalar_mul] at innerEquation
  have baseEquation := congrArg RFAP.QuadraticPair.re innerEquation
  unfold innerScalar at baseEquation
  simp only [RFAP.QuadraticPair.mul_re, RFAP.QuadraticPair.scalar_re,
    RFAP.QuadraticPair.scalar_im, mul_zero, sub_zero] at baseEquation
  have fourNonzero : (4 : K) ≠ 0 := by
    intro fourZero
    have twoProductZero : (2 : K) * 2 = 0 := by
      calc
        (2 : K) * 2 = 4 := by ring1
        _ = 0 := fourZero
    exact (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
      twoProductZero
  apply eq_of_mul_eq_mul_left fourNonzero
  calc
    4 * spreadPolynomial (half + half + 1) value =
        4 * value * oddSpreadRootExpansion half value ^ 2 := baseEquation
    _ = 4 * (value * oddSpreadRootExpansion half value ^ 2) := by ring1

end ExerciseEightSeven

end DivineProportions
