import DivineProportions.Trigonometry.SpreadCyclotomicReduction
import DivineProportions.Trigonometry.SpreadCoefficient
import mathlib.RFAP.FiniteCyclotomicInteger
import mathlib.Tactic.QuotientFreeOmega

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

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace ExerciseEightThirteen
namespace IntegerPolynomial

open RFAP.IntegerPolynomialCertificate

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Rational

/-- The two independently defined finite Lucas recurrences agree. -/
theorem tracePair_lucas_eq_finiteLucas : ∀ index : Nat, ∀ value : K,
    RFAP.FiniteQuadraticNorm.TracePair.lucas index value =
      finiteLucas index value
  | 0, value => rfl
  | 1, value => rfl
  | index + 2, value => by
      rw [RFAP.FiniteQuadraticNorm.TracePair.lucas,
        finiteLucas_succ_succ,
        tracePair_lucas_eq_finiteLucas (index + 1) value,
        tracePair_lucas_eq_finiteLucas index value]

/-- Executable ascending integer coefficients of `S_n`, following the
defining two-step recurrence literally. -/
def spreadPolynomialCoefficients : Nat → List Int
  | 0 => []
  | 1 => [0, 1]
  | index + 2 =>
      add
        (sub
          (mul centeredSpreadSubstitution
            (spreadPolynomialCoefficients (index + 1)))
          (spreadPolynomialCoefficients index))
        [0, 2]

@[simp] theorem spreadPolynomialCoefficients_zero :
    spreadPolynomialCoefficients 0 = [] := rfl

@[simp] theorem spreadPolynomialCoefficients_one :
    spreadPolynomialCoefficients 1 = [0, 1] := rfl

@[simp] theorem spreadPolynomialCoefficients_succ_succ (index : Nat) :
    spreadPolynomialCoefficients (index + 2) =
      add
        (sub
          (mul centeredSpreadSubstitution
            (spreadPolynomialCoefficients (index + 1)))
          (spreadPolynomialCoefficients index))
        [0, 2] := rfl

/-- The coefficient program evaluates to the book's spread polynomial in
every explicit field. -/
theorem eval_spreadPolynomialCoefficients :
    ∀ index : Nat, ∀ value : K,
    eval (spreadPolynomialCoefficients index) value =
      spreadPolynomial index value
  | 0, value => by
      rw [spreadPolynomialCoefficients_zero, eval_nil,
        spreadPolynomial_zero]
  | 1, value => by
      simp only [spreadPolynomialCoefficients_one, eval_cons, eval_nil,
        Int.cast_zero, Int.cast_one, mul_zero, add_zero, zero_add, mul_one,
        spreadPolynomial_one]
  | index + 2, value => by
      rw [spreadPolynomialCoefficients_succ_succ, eval_add, eval_sub,
        eval_mul, eval_centeredSpreadSubstitution,
        eval_spreadPolynomialCoefficients (index + 1) value,
        eval_spreadPolynomialCoefficients index value,
        spreadPolynomial_succ_succ]
      simp only [eval_cons, eval_nil, Int.cast_zero, Int.cast_ofNat,
        mul_zero, add_zero, zero_add]
      ring0

/-- A closed finite coefficient list for `S_n`, extracted from the integral
coefficient formula in Exercise 8.9.  It is used only to certify the exact
degree of the recurrence list above. -/
def spreadDegreeCertificateCoefficients (number : Nat) : List Int :=
  0 :: (List.range number).map fun index =>
    Int.ofNat (spreadArrayCoefficient number (index + 1)) * (-4) ^ index

private theorem eval_append_singleton
    (coefficients : List Int) (coefficient : Int) (value : K) :
    eval (coefficients ++ [coefficient]) value =
      eval coefficients value + (coefficient : K) * value ^ coefficients.length := by
  induction coefficients with
  | nil =>
      simp only [List.nil_append, eval_cons, eval_nil, mul_zero, add_zero,
        List.length_nil, pow_zero, mul_one, zero_add]
  | cons head remaining inductionHypothesis =>
      rw [List.cons_append, eval_cons, inductionHypothesis, eval_cons,
        List.length_cons, pow_succ]
      ring0

private theorem eval_map_range : ∀ (count : Nat) (coefficient : Nat → Int)
    (value : K),
    eval ((List.range count).map coefficient) value =
      RFAP.finitePrefixSum count fun index =>
        (coefficient index : K) * value ^ index
  | 0, coefficient, value => rfl
  | count + 1, coefficient, value => by
      rw [List.range_succ, List.map_append, List.map_singleton,
        eval_append_singleton, List.length_map, List.length_range,
        RFAP.finitePrefixSum_succ_last,
        eval_map_range count coefficient value]

/-- The closed degree certificate evaluates to the same spread polynomial. -/
theorem eval_spreadDegreeCertificateCoefficients
    (number : Nat) (value : K) :
    eval (spreadDegreeCertificateCoefficients number) value =
      spreadPolynomial number value := by
  rw [exercise_8_9_integer_coefficients]
  unfold spreadDegreeCertificateCoefficients spreadCoefficientExpansion
  rw [eval_cons, eval_map_range]
  rw [Int.cast_zero, zero_add]
  calc
    value * RFAP.finitePrefixSum number (fun index =>
          (Int.ofNat (spreadArrayCoefficient number (index + 1)) *
              (-4) ^ index : Int) * value ^ index) =
        value * RFAP.finitePrefixSum number (fun index =>
          (spreadArrayCoefficient number (index + 1) : K) *
            (-4) ^ index * value ^ index) := by
      apply congrArg (value * ·)
      apply RFAP.finitePrefixSum_congr
      intro index _
      rw [QuotientFreeRing.intCast_mul, QuotientFreeRing.intCast_pow,
        Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat]
    _ = RFAP.finitePrefixSum number (fun index =>
          value * ((spreadArrayCoefficient number (index + 1) : K) *
            (-4) ^ index * value ^ index)) :=
      (RFAP.finitePrefixSum_mul_left number value _).symm
    _ = RFAP.finitePrefixSum number (fun index =>
          (spreadArrayCoefficient number (index + 1) : K) * value *
            (-4 * value) ^ index) := by
      apply RFAP.finitePrefixSum_congr
      intro index _
      rw [mul_pow]
      rw [← mul_assoc value
          ((spreadArrayCoefficient number (index + 1) : K) * (-4) ^ index)
          (value ^ index),
        ← mul_assoc value
          (spreadArrayCoefficient number (index + 1) : K) ((-4) ^ index),
        mul_comm value (spreadArrayCoefficient number (index + 1) : K),
        mul_assoc]

theorem spreadDegreeCertificateCoefficients_length (number : Nat) :
    (spreadDegreeCertificateCoefficients number).length = number + 1 := by
  unfold spreadDegreeCertificateCoefficients
  simp only [List.length_cons, List.length_map, List.length_range]

private theorem spreadArrayCoefficient_succ_self (index : Nat) :
    spreadArrayCoefficient (index + 1) (index + 1) = 1 := by
  unfold spreadArrayCoefficient
  rw [RFAP.finite_choose_self,
    Nat.choose_eq_zero_of_lt (by omega0), Nat.add_zero]

theorem spreadDegreeCertificateCoefficients_getLast (index : Nat) :
    (spreadDegreeCertificateCoefficients (index + 1)).getLast? =
      some ((-4) ^ index) := by
  unfold spreadDegreeCertificateCoefficients
  rw [List.range_succ, List.map_append, List.map_singleton]
  simp only [spreadArrayCoefficient_succ_self, Int.ofNat_eq_natCast,
    Int.natCast_one, one_mul]
  let earlierCoefficients := (List.range index).map fun index_1 =>
    Int.ofNat (spreadArrayCoefficient (index + 1) (index_1 + 1)) *
      (-4) ^ index_1
  change (0 :: (earlierCoefficients ++ [(-4) ^ index])).getLast? =
    some ((-4) ^ index)
  rw [show 0 :: (earlierCoefficients ++ [(-4) ^ index]) =
      (0 :: earlierCoefficients) ++ [(-4) ^ index] by rfl,
    List.getLast?_append_of_ne_nil (0 :: earlierCoefficients) (by simp)]
  rfl

private theorem negative_four_pow_ne_zero : ∀ index : Nat,
    ((-4 : Int) ^ index) ≠ 0
  | 0 => by decide
  | index + 1 => by
      rw [pow_succ]
      intro productZero
      rcases Int.mul_eq_zero.mp productZero with previousZero | fourZero
      · exact negative_four_pow_ne_zero index previousZero
      · exact (by decide : (-4 : Int) ≠ 0) fourZero

/-- The recurrence coefficients and the closed coefficient formula represent
the same canonical rational polynomial. -/
theorem ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate
    (number : Nat) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (spreadPolynomialCoefficients number) =
      RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (spreadDegreeCertificateCoefficients number) := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_normalized _)
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_normalized _)
  intro value
  rw [RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    eval_spreadPolynomialCoefficients,
    eval_spreadDegreeCertificateCoefficients]

/-- The represented spread polynomial has exact degree `n`. -/
theorem spreadPolynomialCoefficients_natDegree
    (number : Nat) (positive : 0 < number) :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      (spreadPolynomialCoefficients number)).natDegree = number := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ index =>
      rw [ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate]
      exact RFAP.FiniteIntegerPolynomial.ofAscending_natDegree_of_getLast
        (spreadDegreeCertificateCoefficients_length (index + 1))
        (spreadDegreeCertificateCoefficients_getLast index)
        (negative_four_pow_ne_zero index)

/-- Positive spread polynomials are nonzero in the constructive rational
coefficient model. -/
theorem spreadPolynomialCoefficients_nonzero
    (number : Nat) (positive : 0 < number) :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      (spreadPolynomialCoefficients number)).isZero = false := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ index =>
      rw [ofAscending_spreadPolynomialCoefficients_eq_degreeCertificate]
      exact RFAP.FiniteIntegerPolynomial.ofAscending_isZero_false_of_getLast
        (spreadDegreeCertificateCoefficients_getLast index)
        (negative_four_pow_ne_zero index)

/-- The executable spread-cyclotomic factor.  Index one is the endpoint
factor `s`; every index at least two is the quadratic norm of the finite
ordinary cyclotomic factor after `t = 2 - 4s`. -/
def spreadCyclotomicFactorCoefficients : Nat → List Int
  | 0 => [1]
  | 1 => [0, 1]
  | index + 2 =>
      spreadRealFactorCoefficients
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients (index + 2)))

@[simp] theorem spreadCyclotomicFactorCoefficients_zero :
    spreadCyclotomicFactorCoefficients 0 = [1] := rfl

@[simp] theorem spreadCyclotomicFactorCoefficients_one :
    spreadCyclotomicFactorCoefficients 1 = [0, 1] := rfl

/-- Away from the endpoint, the displayed spread factor is exactly the
substituted quadratic norm. -/
theorem eval_spreadCyclotomicFactorCoefficients_of_two_le
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    eval (spreadCyclotomicFactorCoefficients number) value =
      eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number))
        (2 - 4 * value) := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero => exact False.elim (by omega0)
      | succ index =>
          change
            eval (spreadCyclotomicFactorCoefficients (index + 2)) value =
              eval
                (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
                  (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients
                    (index + 2))) (2 - 4 * value)
          rw [spreadCyclotomicFactorCoefficients,
            eval_spreadRealFactorCoefficients]

/-- A quotient-coordinate slot for all proper non-endpoint divisors.  The
coordinate range is `0,...,n-1`; hence the exceptional quotient `1`, which
occurs at coordinate `n`, is deliberately absent. -/
def properSpreadCyclotomicFactorCoefficients (number : Nat)
    (divisor : Fin number) : List Int :=
  if _selected : 2 ≤ divisor.val ∧ divisor.val ∣ number then
    spreadCyclotomicFactorCoefficients (number / divisor.val)
  else [1]

/-- Product of all proper spread factors except `C_1`. -/
def properSpreadCyclotomicProductCoefficients (number : Nat) : List Int :=
  RFAP.FiniteCyclotomic.coefficientProductFin number
    (properSpreadCyclotomicFactorCoefficients number)

/-- Totient degrees in the same proper non-endpoint quotient-coordinate
slots. -/
def properSpreadCyclotomicTotientSum (number : Nat) : Nat :=
  RFAP.FiniteCyclotomic.sumFinNat number fun divisor =>
    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
      RFAP.finiteTotient (number / divisor.val)
    else 0

/-- The endpoint degree, all proper non-endpoint degrees, and the current
totient degree add to `n`.  This is the exact finite divisor-degree law. -/
theorem endpoint_add_properTotient_add_current
    (number : Nat) (twoLe : 2 ≤ number) :
    1 + properSpreadCyclotomicTotientSum number +
        RFAP.finiteTotient number = number := by
  let whole : Nat → Nat := fun divisor =>
    if RFAP.finiteDivides divisor number then
      RFAP.finiteTotient (number / divisor)
    else 0
  let endpoint : Nat → Nat := fun divisor =>
    if RFAP.finiteNatEquals divisor 1 then
      RFAP.finiteTotient number
    else 0
  let proper : Fin number → Nat := fun divisor =>
    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
      RFAP.finiteTotient (number / divisor.val)
    else 0
  have termSplit (divisor : Fin number) :
      whole divisor.val = proper divisor + endpoint divisor.val := by
    by_cases divides : divisor.val ∣ number
    · dsimp only [whole, proper, endpoint]
      rw [show RFAP.finiteDivides divisor.val number = true by
          exact (RFAP.finiteDivides_eq_true _ _).2 divides]
      by_cases large : 2 ≤ divisor.val
      · have notOne : divisor.val ≠ 1 := by omega0
        have notEndpoint : RFAP.finiteNatEquals divisor.val 1 = false :=
          RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
            notOne ((RFAP.finiteNatEquals_eq_true _ _).1 equal))
        have selected : 2 ≤ divisor.val ∧ divisor.val ∣ number :=
          ⟨large, divides⟩
        simp only [notEndpoint, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero]
        rw [if_pos selected]
      · have positive : 0 < divisor.val := by
          by_contra notPositive
          have zero : divisor.val = 0 := Nat.eq_zero_of_not_pos notPositive
          have numberZero : number = 0 := by
            apply Nat.eq_zero_of_zero_dvd
            rw [← zero]
            exact divides
          omega0
        have one : divisor.val = 1 := by omega0
        have notSelected : ¬(2 ≤ divisor.val ∧ divisor.val ∣ number) :=
          fun selected => large selected.1
        have endpointTrue : RFAP.finiteNatEquals 1 1 = true :=
          (RFAP.finiteNatEquals_eq_true 1 1).2 rfl
        rw [if_neg notSelected, one, Nat.div_one]
        simp only [endpointTrue, ↓reduceIte, Nat.zero_add]
    · dsimp only [whole, proper, endpoint]
      have notSelected : ¬(2 ≤ divisor.val ∧ divisor.val ∣ number) :=
        fun selected => divides selected.2
      have notOne : divisor.val ≠ 1 := by
        intro one
        apply divides
        rw [one]
        exact one_dvd number
      rw [show RFAP.finiteDivides divisor.val number = false by
            exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun truth =>
              divides ((RFAP.finiteDivides_eq_true _ _).1 truth)),
        if_neg notSelected]
      have endpointFalse : RFAP.finiteNatEquals divisor.val 1 = false :=
        RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
          notOne ((RFAP.finiteNatEquals_eq_true _ _).1 equal))
      rw [endpointFalse]
      rfl
  have prefixSplit :
      RFAP.finiteNatSum number whole =
        RFAP.FiniteCyclotomic.sumFinNat number proper +
          RFAP.finiteNatSum number endpoint :=
    RFAP.FiniteCyclotomic.finiteNatSum_eq_sumFinNat_add
      number whole endpoint proper termSplit
  have endpointSum : RFAP.finiteNatSum number endpoint =
      RFAP.finiteTotient number := by
    unfold endpoint
    rw [RFAP.FiniteCyclotomic.finiteNatSum_singletonWeight]
    rw [show RFAP.finiteNatLess 1 number = true by
      exact (RFAP.finiteNatLess_eq_true 1 number).2 twoLe]
    simp
  have total := RFAP.finiteDivisorQuotientTotientSum_eq number
  unfold RFAP.finiteDivisorQuotientTotientSum at total
  change RFAP.finiteNatSum (number + 1) whole = number at total
  rw [RFAP.finiteNatSum_succ_last, prefixSplit, endpointSum] at total
  have finalDivides : RFAP.finiteDivides number number = true :=
    (RFAP.finiteDivides_eq_true number number).2 (dvd_refl number)
  dsimp only [whole] at total
  rw [finalDivides, if_pos rfl, Nat.div_self (by omega0),
    RFAP.finiteTotient_one] at total
  unfold properSpreadCyclotomicTotientSum
  change 1 + RFAP.FiniteCyclotomic.sumFinNat number proper +
      RFAP.finiteTotient number = number
  omega0

/-- The complete divisor product at index `n`. -/
def spreadCyclotomicDivisorProductCoefficients : Nat → List Int
  | 0 => []
  | 1 => [0, 1]
  | number + 2 =>
      mul
        (mul [0, 1]
          (properSpreadCyclotomicProductCoefficients (number + 2)))
        (spreadCyclotomicFactorCoefficients (number + 2))

/-- Evaluation of a `Fin`-indexed coefficient product respects pointwise
equality, even when its two sides are evaluated at different points. -/
theorem eval_coefficientProductFin_congr : ∀ (count : Nat)
    (left right : Fin count → List Int) (leftPoint rightPoint : K),
    (∀ index, eval (left index) leftPoint =
      eval (right index) rightPoint) →
    eval (RFAP.FiniteCyclotomic.coefficientProductFin count left)
        leftPoint =
      eval (RFAP.FiniteCyclotomic.coefficientProductFin count right)
        rightPoint
  | 0, left, right, leftPoint, rightPoint, pointwise => by
      simp only [RFAP.FiniteCyclotomic.coefficientProductFin_zero,
        eval_cons, eval_nil, Int.cast_one, mul_zero, add_zero]
  | count + 1, left, right, leftPoint, rightPoint, pointwise => by
      rw [RFAP.FiniteCyclotomic.coefficientProductFin_succ,
        RFAP.FiniteCyclotomic.coefficientProductFin_succ,
        eval_mul, eval_mul,
        eval_coefficientProductFin_congr count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc) leftPoint rightPoint
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]

/-- Taking the finite quadratic norm commutes with a finite coefficient
product after evaluation. -/
theorem eval_norm_coefficientProductFin : ∀ (count : Nat)
    (factor : Fin count → List Int) (trace : K),
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.coefficientProductFin count factor)) trace =
      eval
        (RFAP.FiniteCyclotomic.coefficientProductFin count fun index =>
          RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (factor index)) trace
  | 0, factor, trace => by
      rw [RFAP.FiniteCyclotomic.coefficientProductFin_zero,
        RFAP.FiniteCyclotomic.coefficientProductFin_zero,
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients]
      simp [RFAP.FiniteQuadraticNorm.TracePair.eval,
        RFAP.FiniteQuadraticNorm.TracePair.norm,
        RFAP.FiniteQuadraticNorm.TracePair.zero]
  | count + 1, factor, trace => by
      rw [RFAP.FiniteCyclotomic.coefficientProductFin_succ,
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients_mul,
        RFAP.FiniteCyclotomic.coefficientProductFin_succ, eval_mul,
        eval_norm_coefficientProductFin count
          (fun index => factor index.castSucc) trace]

/-- The first finite ordinary cyclotomic factor is `X-1`. -/
theorem finiteCyclotomic_one_eq_powerMinusOne_one :
    RFAP.FiniteCyclotomic.finiteCyclotomic 1 =
      RFAP.FiniteCyclotomic.powerMinusOne 1 := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (RFAP.FiniteCyclotomic.finiteCyclotomic_stageSpec 1 (by omega0)).normalized
    (RFAP.FiniteCyclotomic.powerMinusOne_normalized 1)
  intro point
  have factorization :=
    (RFAP.FiniteCyclotomic.finiteCyclotomic_stageSpec 1 (by omega0)).factorization
      point
  have properValue :
      (RFAP.FiniteCyclotomic.properCyclotomicProduct 1).eval point = 1 := by
    unfold RFAP.FiniteCyclotomic.properCyclotomicProduct
    rw [RFAP.FiniteCyclotomic.productFin_succ,
      RFAP.FiniteCyclotomic.productFin_succ,
      RFAP.FiniteCyclotomic.productFin_zero]
    simp only [RFAP.FiniteCyclotomic.properCyclotomicFactor,
      Fin.val_last, Fin.val_castSucc]
    rw [dif_neg (by omega0), dif_neg (by omega0)]
    simp only [RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.ComputablePolynomial.DensePolynomial.eval_constant, one_mul]
  rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
    properValue, one_mul] at factorization
  exact factorization.symm

/-- The exceptional endpoint norm contributes exactly `4s`. -/
theorem eval_norm_finiteCyclotomicCoefficients_one (value : K) :
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients 1))
        (2 - 4 * value) =
      4 * value := by
  have coefficientIdentity :
      RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients 1) =
        RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            1) := by
    rw [RFAP.FiniteCyclotomic.ofAscending_finiteCyclotomicCoefficients
        1 (by omega0),
      RFAP.FiniteCyclotomic.ofAscending_powerMinusOneCoefficients,
      finiteCyclotomic_one_eq_powerMinusOne_one]
  have pairIdentity :=
    RFAP.FiniteQuadraticNorm.TracePair.eval_eq_of_ofAscending_eq
      coefficientIdentity (2 - 4 * value)
  calc
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients 1))
        (2 - 4 * value) =
      RFAP.FiniteQuadraticNorm.TracePair.norm (2 - 4 * value)
        (RFAP.FiniteQuadraticNorm.TracePair.eval
          (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients 1)
          (2 - 4 * value)) :=
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients _ _
    _ = RFAP.FiniteQuadraticNorm.TracePair.norm (2 - 4 * value)
        (RFAP.FiniteQuadraticNorm.TracePair.eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            1) (2 - 4 * value)) := by
          rw [pairIdentity]
    _ = eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            1)) (2 - 4 * value) :=
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients
          _ _).symm
    _ = 2 - RFAP.FiniteQuadraticNorm.TracePair.lucas 1
          (2 - 4 * value) :=
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_norm_powerMinusOneCoefficients
          1 (2 - 4 * value)
    _ = 4 * value := by
      rw [RFAP.FiniteQuadraticNorm.TracePair.lucas]
      ring0

/-- Each non-endpoint quotient slot has the same norm as its spread-factor
counterpart. -/
theorem eval_norm_properCyclotomicFactorCoefficients
    (number : Nat) (divisor : Fin number) (value : K) :
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.properCyclotomicFactorCoefficients
            number divisor.castSucc)) (2 - 4 * value) =
      eval (properSpreadCyclotomicFactorCoefficients number divisor) value := by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · have selectedCast :
        2 ≤ divisor.castSucc.val ∧ divisor.castSucc.val ∣ number := by
      simpa only [Fin.val_castSucc] using selected
    rw [RFAP.FiniteCyclotomic.properCyclotomicFactorCoefficients,
      dif_pos selectedCast, properSpreadCyclotomicFactorCoefficients,
      dif_pos selected]
    have quotientTwoLe : 2 ≤ number / divisor.val :=
      RFAP.FiniteCyclotomic.divisorQuotient_two_le
        (by omega0) selected.2 divisor.isLt
    exact
      (eval_spreadCyclotomicFactorCoefficients_of_two_le
        (number / divisor.val) quotientTwoLe value).symm
  · have selectedCast :
        ¬(2 ≤ divisor.castSucc.val ∧ divisor.castSucc.val ∣ number) := by
      simpa only [Fin.val_castSucc] using selected
    rw [RFAP.FiniteCyclotomic.properCyclotomicFactorCoefficients,
      dif_neg selectedCast, properSpreadCyclotomicFactorCoefficients,
      dif_neg selected,
      RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients]
    simp [RFAP.FiniteQuadraticNorm.TracePair.eval,
      RFAP.FiniteQuadraticNorm.TracePair.norm,
      RFAP.FiniteQuadraticNorm.TracePair.zero]

/-- The norm of the proper ordinary divisor product is `4s` times the
product of all proper non-endpoint spread factors. -/
theorem eval_norm_properCyclotomicProductCoefficients
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients number))
        (2 - 4 * value) =
      4 * value *
        eval (properSpreadCyclotomicProductCoefficients number) value := by
  unfold RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
    properSpreadCyclotomicProductCoefficients
  rw [RFAP.FiniteCyclotomic.coefficientProductFin_succ,
    RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients_mul,
    eval_norm_coefficientProductFin]
  have prefixIdentity := eval_coefficientProductFin_congr number
    (fun divisor =>
      RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
        (RFAP.FiniteCyclotomic.properCyclotomicFactorCoefficients
          number divisor.castSucc))
    (properSpreadCyclotomicFactorCoefficients number)
    (2 - 4 * value) value
    (fun divisor =>
      eval_norm_properCyclotomicFactorCoefficients
        number divisor value)
  rw [prefixIdentity]
  have lastSelected : 2 ≤ (Fin.last number).val ∧
      (Fin.last number).val ∣ number := by
    simp only [Fin.val_last]
    exact ⟨twoLe, dvd_refl number⟩
  rw [RFAP.FiniteCyclotomic.properCyclotomicFactorCoefficients,
    dif_pos lastSelected, Fin.val_last, Nat.div_self (by omega0),
    eval_norm_finiteCyclotomicCoefficients_one]
  ring0

/-- The ordinary coefficient factorization remains valid after applying the
finite quadratic norm. -/
theorem eval_norm_finiteCyclotomic_factorization
    (number : Nat) (positive : 0 < number) (trace : K) :
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            number)) trace =
      eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
              number)) trace *
        eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number))
          trace := by
  have pairIdentity :=
    RFAP.FiniteQuadraticNorm.TracePair.eval_eq_of_ofAscending_eq
      (RFAP.FiniteCyclotomic.finiteCyclotomic_factorization_coefficients
        number positive) trace
  rw [RFAP.FiniteQuadraticNorm.TracePair.eval_mul] at pairIdentity
  calc
    eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            number)) trace =
      RFAP.FiniteQuadraticNorm.TracePair.norm trace
        (RFAP.FiniteQuadraticNorm.TracePair.eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            number) trace) :=
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients _ _
    _ = RFAP.FiniteQuadraticNorm.TracePair.norm trace
        (RFAP.FiniteQuadraticNorm.TracePair.mul trace
          (RFAP.FiniteQuadraticNorm.TracePair.eval
            (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
              number) trace)
          (RFAP.FiniteQuadraticNorm.TracePair.eval
            (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number)
            trace)) := by rw [pairIdentity]
    _ = RFAP.FiniteQuadraticNorm.TracePair.norm trace
          (RFAP.FiniteQuadraticNorm.TracePair.eval
            (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
              number) trace) *
        RFAP.FiniteQuadraticNorm.TracePair.norm trace
          (RFAP.FiniteQuadraticNorm.TracePair.eval
            (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number)
            trace) :=
      RFAP.FiniteQuadraticNorm.TracePair.norm_mul _ _ _
    _ = eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
              number)) trace *
        eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number))
          trace := by
      rw [RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients,
        RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_normCoefficients]

/-- Division-free form of the full factorization.  It is valid directly in
every explicit field, including characteristics two and four's divisors. -/
theorem spreadCyclotomic_factorization_cleared
    (number : Nat) (twoLe : 2 ≤ number) (value : K) :
    4 * spreadPolynomial number value =
      4 * eval (spreadCyclotomicDivisorProductCoefficients number) value := by
  have positive : 0 < number := by omega0
  have normFactorization := eval_norm_finiteCyclotomic_factorization
    (K := K) number positive (2 - 4 * value)
  calc
    4 * spreadPolynomial number value =
        2 - finiteLucas number (2 - 4 * value) :=
      spread_lucas_cleared number value
    _ = 2 - RFAP.FiniteQuadraticNorm.TracePair.lucas number
          (2 - 4 * value) := by
      rw [tracePair_lucas_eq_finiteLucas]
    _ = eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
            number)) (2 - 4 * value) :=
      (RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_norm_powerMinusOneCoefficients
        number (2 - 4 * value)).symm
    _ = eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.properCyclotomicProductCoefficients
              number))
          (2 - 4 * value) *
        eval
          (RFAP.FiniteQuadraticNorm.IntegerPolynomial.normCoefficients
            (RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients number))
          (2 - 4 * value) := normFactorization
    _ = (4 * value *
          eval (properSpreadCyclotomicProductCoefficients number) value) *
        eval (spreadCyclotomicFactorCoefficients number) value := by
      rw [eval_norm_properCyclotomicProductCoefficients number twoLe value,
        ← eval_spreadCyclotomicFactorCoefficients_of_two_le
          number twoLe value]
    _ = 4 * eval (spreadCyclotomicDivisorProductCoefficients number) value := by
      cases number with
      | zero => exact False.elim (by omega0)
      | succ previous =>
          cases previous with
          | zero => exact False.elim (by omega0)
          | succ index =>
              change
                4 * value *
                      eval
                        (properSpreadCyclotomicProductCoefficients
                          (index + 2)) value *
                    eval (spreadCyclotomicFactorCoefficients (index + 2))
                      value =
                  4 * eval
                    (spreadCyclotomicDivisorProductCoefficients (index + 2))
                    value
              rw [spreadCyclotomicDivisorProductCoefficients, eval_mul,
                eval_mul]
              simp only [eval_cons, eval_nil, Int.cast_zero, Int.cast_one,
                mul_zero, add_zero, zero_add, mul_one]
              ring0

private theorem rational_four_ne_zero : (4 : Rational) ≠ 0 := by
  intro equality
  exact (by decide : (4 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct equality)

private theorem rational_eq_of_four_mul_eq
    {left right : Rational} (equal : 4 * left = 4 * right) : left = right := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne rational_four_ne_zero
  simpa only [mul_comm] using equal

/-- The general factorization as an integer coefficient identity.  This is
the characteristic-independent artifact transported below. -/
theorem ofAscending_spreadCyclotomic_factorization
    (number : Nat) (positive : 0 < number) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (spreadPolynomialCoefficients number) =
      RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (spreadCyclotomicDivisorProductCoefficients number) := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_normalized _)
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_normalized _)
  intro value
  rw [RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    eval_spreadPolynomialCoefficients]
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero =>
          simp only [spreadCyclotomicDivisorProductCoefficients,
            spreadPolynomial_one, eval_cons, eval_nil, Int.cast_zero,
            Int.cast_one, mul_zero, add_zero, zero_add, mul_one]
      | succ index =>
          apply rational_eq_of_four_mul_eq
          exact spreadCyclotomic_factorization_cleared
            (K := Rational) (index + 2) (by omega0) value

/-- Exercise 8.13 for every positive finite index and every explicit field:
`S_n` is exactly the executable product of its spread-cyclotomic factors. -/
theorem exercise_8_13_general
    (number : Nat) (positive : 0 < number) (value : K) :
    spreadPolynomial number value =
      eval (spreadCyclotomicDivisorProductCoefficients number) value := by
  have transported :=
    RFAP.FiniteIntegerPolynomial.eval_eq_of_ofAscending_eq
      (ofAscending_spreadCyclotomic_factorization number positive) value
  rw [eval_spreadPolynomialCoefficients] at transported
  exact transported

/-- Canonical constructive-rational polynomial represented by `C_n`. -/
def spreadCyclotomicFactorPolynomial (number : Nat) : Polynomial :=
  RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
    (spreadCyclotomicFactorCoefficients number)

/-- Canonical polynomial for the proper non-endpoint product. -/
def properSpreadCyclotomicProductPolynomial (number : Nat) : Polynomial :=
  RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
    (properSpreadCyclotomicProductCoefficients number)

/-- The proper coefficient program is the corresponding finite polynomial
product. -/
theorem properSpreadCyclotomicProductPolynomial_eq_productFin
    (number : Nat) :
    properSpreadCyclotomicProductPolynomial number =
      RFAP.FiniteCyclotomic.productFin number fun divisor =>
        RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
          (properSpreadCyclotomicFactorCoefficients number divisor) := by
  unfold properSpreadCyclotomicProductPolynomial
    properSpreadCyclotomicProductCoefficients
  exact RFAP.FiniteCyclotomic.ofAscending_coefficientProductFin _ _

/-- For `n >= 2`, the complete coefficient program visibly consists of the
endpoint, the proper non-endpoint product, and the current factor. -/
theorem ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
    (number : Nat) (twoLe : 2 ≤ number) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (spreadCyclotomicDivisorProductCoefficients number) =
      (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending [0, 1] *
          properSpreadCyclotomicProductPolynomial number) *
        spreadCyclotomicFactorPolynomial number := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero => exact False.elim (by omega0)
      | succ index =>
          change
            RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                (mul
                  (mul [0, 1]
                    (properSpreadCyclotomicProductCoefficients (index + 2)))
                  (spreadCyclotomicFactorCoefficients (index + 2))) =
              (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                    [0, 1] *
                  RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                    (properSpreadCyclotomicProductCoefficients (index + 2))) *
                RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                  (spreadCyclotomicFactorCoefficients (index + 2))
          rw [RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_mul,
            RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_mul]

private theorem endpointPolynomial_natDegree :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      [0, 1]).natDegree = 1 :=
  RFAP.FiniteIntegerPolynomial.ofAscending_natDegree_of_getLast
    (coefficients := [0, 1]) (degree := 1) (leading := 1)
    (by decide) (by decide) (by decide)

private theorem endpointPolynomial_nonzero :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      [0, 1]).isZero = false :=
  RFAP.FiniteIntegerPolynomial.ofAscending_isZero_false_of_getLast
    (coefficients := [0, 1]) (leading := 1) (by decide) (by decide)

private theorem constantOnePolynomial_natDegree :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      [1]).natDegree = 0 :=
  RFAP.FiniteIntegerPolynomial.ofAscending_natDegree_of_getLast
    (coefficients := [1]) (degree := 0) (leading := 1)
    (by decide) (by decide) (by decide)

private theorem constantOnePolynomial_nonzero :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      [1]).isZero = false :=
  RFAP.FiniteIntegerPolynomial.ofAscending_isZero_false_of_getLast
    (coefficients := [1]) (leading := 1) (by decide) (by decide)

/-- Every positive spread-cyclotomic factor is nonzero.  This follows
constructively from the already proved factorization and the explicit
nonzero leading coefficient of `S_n`. -/
theorem spreadCyclotomicFactorPolynomial_nonzero
    (number : Nat) (positive : 0 < number) :
    (spreadCyclotomicFactorPolynomial number).isZero = false := by
  cases number with
  | zero => exact False.elim (by omega0)
  | succ previous =>
      cases previous with
      | zero =>
          unfold spreadCyclotomicFactorPolynomial
          rw [spreadCyclotomicFactorCoefficients_one]
          exact endpointPolynomial_nonzero
      | succ index =>
          let number := index + 2
          have twoLe : 2 ≤ number := by omega0
          cases zeroTest : (spreadCyclotomicFactorPolynomial number).isZero with
          | false => rfl
          | true =>
              have represented :=
                ofAscending_spreadCyclotomic_factorization number (by omega0)
              have divisorShape :=
                ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
                  number twoLe
              have productZero :
                  (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                        [0, 1] *
                      properSpreadCyclotomicProductPolynomial number) *
                    spreadCyclotomicFactorPolynomial number = 0 :=
                RFAP.ComputablePolynomial.DensePolynomial.mul_eq_zero_of_isZero_right
                  zeroTest
              have spreadZero :
                  RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                      (spreadPolynomialCoefficients number) = 0 :=
                represented.trans (divisorShape.trans productZero)
              have zeroTests := congrArg
                RFAP.ComputablePolynomial.DensePolynomial.isZero spreadZero
              rw [spreadPolynomialCoefficients_nonzero number (by omega0),
                RFAP.ComputablePolynomial.DensePolynomial.isZero_zero]
                at zeroTests
              exact Bool.noConfusion zeroTests

/-- Each proper non-endpoint slot is nonzero. -/
theorem properSpreadCyclotomicFactorPolynomial_nonzero
    (number : Nat) (positive : 0 < number) (divisor : Fin number) :
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
      (properSpreadCyclotomicFactorCoefficients number divisor)).isZero =
        false := by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · rw [properSpreadCyclotomicFactorCoefficients, dif_pos selected]
    exact spreadCyclotomicFactorPolynomial_nonzero
      (number / divisor.val)
      (RFAP.FiniteCyclotomic.divisorQuotient_positive positive selected.2)
  · rw [properSpreadCyclotomicFactorCoefficients, dif_neg selected]
    exact constantOnePolynomial_nonzero

/-- The constructive spread-cyclotomic factor has exactly Euler-totient
degree, completing the degree clause of Exercise 8.13. -/
theorem spreadCyclotomicFactorPolynomial_natDegree :
    ∀ number : Nat, 0 < number →
      (spreadCyclotomicFactorPolynomial number).natDegree =
        RFAP.finiteTotient number := by
  intro number
  induction number using Nat.strong_induction_on with
  | h number inductionHypothesis =>
      intro positive
      cases number with
      | zero => exact False.elim ((Nat.not_lt_zero 0) positive)
      | succ previous =>
          cases previous with
          | zero =>
              unfold spreadCyclotomicFactorPolynomial
              rw [spreadCyclotomicFactorCoefficients_one,
                RFAP.finiteTotient_one]
              exact endpointPolynomial_natDegree
          | succ index =>
              let number := index + 2
              have numberPositive : 0 < number := by omega0
              have twoLe : 2 ≤ number := by omega0
              let slotPolynomial : Fin number → Polynomial := fun divisor =>
                RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                  (properSpreadCyclotomicFactorCoefficients number divisor)
              have slotNonzero (divisor : Fin number) :
                  (slotPolynomial divisor).isZero = false := by
                exact properSpreadCyclotomicFactorPolynomial_nonzero
                  number numberPositive divisor
              have slotDegree (divisor : Fin number) :
                  (slotPolynomial divisor).natDegree =
                    if 2 ≤ divisor.val ∧ divisor.val ∣ number then
                      RFAP.finiteTotient (number / divisor.val)
                    else 0 := by
                by_cases selected :
                    2 ≤ divisor.val ∧ divisor.val ∣ number
                · unfold slotPolynomial
                  rw [properSpreadCyclotomicFactorCoefficients,
                    dif_pos selected, if_pos selected]
                  exact inductionHypothesis (number / divisor.val)
                    (Nat.div_lt_self numberPositive (by omega0))
                    (RFAP.FiniteCyclotomic.divisorQuotient_positive
                      numberPositive selected.2)
                · unfold slotPolynomial
                  rw [properSpreadCyclotomicFactorCoefficients,
                    dif_neg selected, if_neg selected]
                  exact constantOnePolynomial_natDegree
              have properNonzero :
                  (properSpreadCyclotomicProductPolynomial number).isZero =
                    false := by
                rw [properSpreadCyclotomicProductPolynomial_eq_productFin]
                exact RFAP.FiniteCyclotomic.productFin_nonzero
                  number slotPolynomial slotNonzero
              have properDegree :
                  (properSpreadCyclotomicProductPolynomial number).natDegree =
                    properSpreadCyclotomicTotientSum number := by
                rw [properSpreadCyclotomicProductPolynomial_eq_productFin,
                  RFAP.FiniteCyclotomic.natDegree_productFin
                    number slotPolynomial slotNonzero]
                unfold properSpreadCyclotomicTotientSum
                apply RFAP.FiniteCyclotomic.sumFinNat_congr
                intro divisor
                exact slotDegree divisor
              have currentNonzero :=
                spreadCyclotomicFactorPolynomial_nonzero
                  number numberPositive
              have endpointProperNonzero :
                  (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
                        [0, 1] *
                      properSpreadCyclotomicProductPolynomial number).isZero =
                    false :=
                RFAP.ComputablePolynomial.DensePolynomial.isZero_mul_eq_false
                  endpointPolynomial_nonzero properNonzero
              have represented :=
                (ofAscending_spreadCyclotomic_factorization
                  number numberPositive).trans
                    (ofAscending_divisorProduct_eq_endpoint_mul_proper_mul_current
                      number twoLe)
              have degreeIdentity := congrArg
                RFAP.ComputablePolynomial.DensePolynomial.natDegree represented
              rw [spreadPolynomialCoefficients_natDegree number numberPositive,
                RFAP.ComputablePolynomial.DensePolynomial.natDegree_mul
                  endpointProperNonzero currentNonzero,
                RFAP.ComputablePolynomial.DensePolynomial.natDegree_mul
                  endpointPolynomial_nonzero properNonzero,
                endpointPolynomial_natDegree, properDegree] at degreeIdentity
              have totalDegree :=
                endpoint_add_properTotient_add_current number twoLe
              change
                (spreadCyclotomicFactorPolynomial number).natDegree =
                  RFAP.finiteTotient number
              omega0

end IntegerPolynomial
end ExerciseEightThirteen
end DivineProportions
