import mathlib.RFAP.FiniteIntegerPolynomial
import mathlib.RFAP.FiniteQuadraticNorm
import mathlib.Tactic.QuotientFreeOmega

/-!
# Monic integer coefficients for the finite cyclotomic construction

The rational long-division factors constructed in `FiniteCyclotomic` are
shown here to be monic and to carry executable ascending integer coefficient
lists.  The proof is a second primitive recursion over the already verified
factorization; it uses the finite monic-division theorem rather than a UFD or
root factorization.
-/

namespace RFAP.FiniteCyclotomic

open RFAP.ComputablePolynomial.DensePolynomial

namespace IntegerBridge

open RFAP.FiniteIntegerPolynomial

theorem monomialOne_integral : ∀ degree : Nat,
    IsIntegralPolynomial (monomialOne degree)
  | 0 => by
      rw [monomialOne_zero]
      exact integral_constant (integral_of_integer 1)
  | degree + 1 => by
      rw [monomialOne_succ]
      exact integral_shift 1 (monomialOne_integral degree)

theorem powerMinusOne_integral (degree : Nat) :
    IsIntegralPolynomial (powerMinusOne degree) := by
  rw [powerMinusOne]
  exact integral_sub (monomialOne_integral degree)
    (integral_constant (integral_of_integer 1))

theorem leadingCoeff_constant_one :
    (constant (1 : Rational)).leadingCoeff = 1 := by
  unfold leadingCoeff
  rw [normalize_constant_of_ne
    RFAP.ConstructiveFraction.zero_ne_one.symm]
  rfl

theorem leadingCoeff_productFin_one : ∀ (count : Nat)
    (factor : Fin count → Polynomial),
    (∀ index, (factor index).isZero = false) →
    (∀ index, (factor index).leadingCoeff = 1) →
    (productFin count factor).leadingCoeff = 1
  | 0, factor, allNonzero, allMonic => leadingCoeff_constant_one
  | count + 1, factor, allNonzero, allMonic => by
      rw [productFin_succ,
        leadingCoeff_mul
          (productFin_nonzero count (fun index => factor index.castSucc)
            (fun index => allNonzero index.castSucc))
          (allNonzero (Fin.last count)),
        leadingCoeff_productFin_one count
          (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc)
          (fun index => allMonic index.castSucc),
        allMonic (Fin.last count), one_mul]

/-- Every positive finite cyclotomic quotient is monic. -/
theorem finiteCyclotomic_leadingCoeff : ∀ number : Nat, 0 < number →
    (finiteCyclotomic number).leadingCoeff = 1
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have factorMonic (index : Fin (previous + 2)) :
          (properCyclotomicFactor (previous + 1) index).leadingCoeff = 1 := by
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [properCyclotomicFactor, dif_pos selected]
          exact finiteCyclotomic_leadingCoeff
            ((previous + 1) / index.val)
            (divisorQuotient_positive positive selected.2)
        · rw [properCyclotomicFactor, dif_neg selected]
          exact leadingCoeff_constant_one
      have properMonic :
          (properCyclotomicProduct (previous + 1)).leadingCoeff = 1 := by
        rw [properCyclotomicProduct]
        exact leadingCoeff_productFin_one (previous + 2)
          (properCyclotomicFactor (previous + 1))
          (properCyclotomicFactor_nonzero (previous + 1) positive)
          factorMonic
      have stage := finiteCyclotomic_stageSpec (previous + 1) positive
      have representedFactorization : powerMinusOne (previous + 1) =
          properCyclotomicProduct (previous + 1) *
            finiteCyclotomic (previous + 1) :=
        RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
          (powerMinusOne_normalized (previous + 1)) (normalize_mul _ _)
          stage.factorization
      have leadingIdentity := congrArg
        (fun polynomial : Polynomial => polynomial.leadingCoeff)
        representedFactorization
      rw [powerMinusOne_leadingCoeff previous,
        leadingCoeff_mul
          (properCyclotomicProduct_nonzero (previous + 1) positive)
          stage.nonzero,
        properMonic, one_mul] at leadingIdentity
      exact leadingIdentity.symm
termination_by number => number
decreasing_by all_goals exact Nat.div_lt_self (by omega0) (by omega0)

/-- The proper product is monic; exposed separately for long division and
the real-cyclotomic reduction. -/
theorem finiteCyclotomic_leadingCoeff_product (previous : Nat)
    (positive : 0 < previous + 1) :
    (properCyclotomicProduct (previous + 1)).leadingCoeff = 1 := by
  rw [properCyclotomicProduct]
  apply leadingCoeff_productFin_one
  · exact properCyclotomicFactor_nonzero (previous + 1) positive
  · intro index
    by_cases selected :
        2 ≤ index.val ∧ index.val ∣ previous + 1
    · rw [properCyclotomicFactor, dif_pos selected]
      exact finiteCyclotomic_leadingCoeff _
        (divisorQuotient_positive positive selected.2)
    · rw [properCyclotomicFactor, dif_neg selected]
      exact leadingCoeff_constant_one

theorem integral_productFin : ∀ (count : Nat)
    (factor : Fin count → Polynomial),
    (∀ index, IsIntegralPolynomial (factor index)) →
    IsIntegralPolynomial (productFin count factor)
  | 0, factor, allIntegral => by
      exact integral_constant (integral_of_integer 1)
  | count + 1, factor, allIntegral => by
      rw [productFin_succ]
      exact integral_mul
        (integral_productFin count (fun index => factor index.castSucc)
          (fun index => allIntegral index.castSucc))
        (allIntegral (Fin.last count))

/-- Every positive finite cyclotomic quotient has integer coefficients. -/
theorem finiteCyclotomic_integral : ∀ number : Nat, 0 < number →
    IsIntegralPolynomial (finiteCyclotomic number)
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have factorIntegral (index : Fin (previous + 2)) :
          IsIntegralPolynomial
            (properCyclotomicFactor (previous + 1) index) := by
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [properCyclotomicFactor, dif_pos selected]
          exact finiteCyclotomic_integral
            ((previous + 1) / index.val)
            (divisorQuotient_positive positive selected.2)
        · rw [properCyclotomicFactor, dif_neg selected]
          exact integral_constant (integral_of_integer 1)
      have properIntegral : IsIntegralPolynomial
          (properCyclotomicProduct (previous + 1)) := by
        rw [properCyclotomicProduct]
        exact integral_productFin (previous + 2)
          (properCyclotomicFactor (previous + 1)) factorIntegral
      rw [finiteCyclotomic_succ]
      exact divMod_quotient_integral _ _
        (powerMinusOne_integral (previous + 1)) properIntegral
        (by
          exact finiteCyclotomic_leadingCoeff_product previous positive)
termination_by number => number
decreasing_by all_goals exact Nat.div_lt_self (by omega0) (by omega0)

end IntegerBridge

/-- Canonical executable ascending integer coefficients of `Φₙ`. -/
def finiteCyclotomicCoefficients (number : Nat) : List Int :=
  RFAP.FiniteIntegerPolynomial.integerCoefficients
    (finiteCyclotomic number)

theorem ofAscending_finiteCyclotomicCoefficients (number : Nat)
    (positive : 0 < number) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (finiteCyclotomicCoefficients number) =
      finiteCyclotomic number := by
  unfold finiteCyclotomicCoefficients
  rw [RFAP.FiniteIntegerPolynomial.ofAscending_integerCoefficients_eq_normalize
    _ (IntegerBridge.finiteCyclotomic_integral number positive)]
  exact (finiteCyclotomic_stageSpec number positive).normalized

@[simp] theorem eval_finiteCyclotomicCoefficients (number : Nat)
    (positive : 0 < number) (point : Rational) :
    RFAP.IntegerPolynomialCertificate.eval
        (finiteCyclotomicCoefficients number) point =
      (finiteCyclotomic number).eval point := by
  rw [← RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    ofAscending_finiteCyclotomicCoefficients number positive]

/-- Product of a `Fin`-indexed family of ascending integer polynomials. -/
def coefficientProductFin : (count : Nat) →
    (Fin count → List Int) → List Int
  | 0, _ => [1]
  | count + 1, factor =>
      RFAP.IntegerPolynomialCertificate.mul
        (coefficientProductFin count
          (fun index => factor index.castSucc))
        (factor (Fin.last count))

@[simp] theorem coefficientProductFin_zero (factor : Fin 0 → List Int) :
    coefficientProductFin 0 factor = [1] := rfl

@[simp] theorem coefficientProductFin_succ
    (factor : Fin (count + 1) → List Int) :
    coefficientProductFin (count + 1) factor =
      RFAP.IntegerPolynomialCertificate.mul
        (coefficientProductFin count
          (fun index => factor index.castSucc))
        (factor (Fin.last count)) := rfl

theorem ofAscending_coefficientProductFin : ∀ (count : Nat)
    (factor : Fin count → List Int),
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (coefficientProductFin count factor) =
      productFin count (fun index =>
        RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
          (factor index))
  | 0, factor => RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_one
  | count + 1, factor => by
      rw [coefficientProductFin_succ,
        RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_mul,
        ofAscending_coefficientProductFin count
          (fun index => factor index.castSucc), productFin_succ]

/-- Coefficient list in one quotient-coordinate slot of the proper product. -/
def properCyclotomicFactorCoefficients (number : Nat)
    (divisor : Fin (number + 1)) : List Int :=
  if _selected : 2 ≤ divisor.val ∧ divisor.val ∣ number then
    finiteCyclotomicCoefficients (number / divisor.val)
  else [1]

theorem ofAscending_properCyclotomicFactorCoefficients
    (number : Nat) (positive : 0 < number)
    (divisor : Fin (number + 1)) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (properCyclotomicFactorCoefficients number divisor) =
      properCyclotomicFactor number divisor := by
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number
  · rw [properCyclotomicFactorCoefficients, dif_pos selected,
      properCyclotomicFactor, dif_pos selected]
    exact ofAscending_finiteCyclotomicCoefficients _
      (divisorQuotient_positive positive selected.2)
  · rw [properCyclotomicFactorCoefficients, dif_neg selected,
      properCyclotomicFactor, dif_neg selected]
    exact RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_one

/-- Ascending integer coefficients of the complete proper divisor product. -/
def properCyclotomicProductCoefficients (number : Nat) : List Int :=
  coefficientProductFin (number + 1)
    (properCyclotomicFactorCoefficients number)

theorem ofAscending_properCyclotomicProductCoefficients
    (number : Nat) (positive : 0 < number) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (properCyclotomicProductCoefficients number) =
      properCyclotomicProduct number := by
  rw [properCyclotomicProductCoefficients,
    ofAscending_coefficientProductFin, properCyclotomicProduct]
  apply productFin_congr
  intro divisor
  exact ofAscending_properCyclotomicFactorCoefficients number positive divisor

theorem ofAscending_powerMinusOneCoefficients (number : Nat) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
          number) =
      powerMinusOne number := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_normalized _)
    (powerMinusOne_normalized number)
  intro point
  rw [RFAP.FiniteIntegerPolynomial.IntegerPolynomial.eval_ofAscending,
    RFAP.FiniteQuadraticNorm.IntegerPolynomial.eval_powerMinusOneCoefficients,
    eval_powerMinusOne]

/-- Coefficient form of the complete finite divisor factorization of
`X^n-1`. -/
theorem finiteCyclotomic_factorization_coefficients
    (number : Nat) (positive : 0 < number) :
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
          number) =
      RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (RFAP.IntegerPolynomialCertificate.mul
          (properCyclotomicProductCoefficients number)
          (finiteCyclotomicCoefficients number)) := by
  calc
    RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
          number) = powerMinusOne number :=
      ofAscending_powerMinusOneCoefficients number
    _ = properCyclotomicProduct number * finiteCyclotomic number :=
      RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
        (powerMinusOne_normalized number) (normalize_mul _ _)
        (finiteCyclotomic_stageSpec number positive).factorization
    _ = RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending
        (RFAP.IntegerPolynomialCertificate.mul
          (properCyclotomicProductCoefficients number)
          (finiteCyclotomicCoefficients number)) := by
      rw [RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending_mul,
        ofAscending_properCyclotomicProductCoefficients number positive,
        ofAscending_finiteCyclotomicCoefficients number positive]

/-- The divisor factorization evaluates in every explicit field, including
finite characteristic, because it has already been reduced to an integer
coefficient identity. -/
theorem eval_finiteCyclotomic_factorization_coefficients
    {K : Type*} [RFAP.ExplicitField K]
    (number : Nat) (positive : 0 < number) (point : K) :
    RFAP.IntegerPolynomialCertificate.eval
        (RFAP.FiniteQuadraticNorm.IntegerPolynomial.powerMinusOneCoefficients
          number) point =
      RFAP.IntegerPolynomialCertificate.eval
          (properCyclotomicProductCoefficients number) point *
        RFAP.IntegerPolynomialCertificate.eval
          (finiteCyclotomicCoefficients number) point := by
  have transported := RFAP.FiniteIntegerPolynomial.eval_eq_of_ofAscending_eq
    (finiteCyclotomic_factorization_coefficients number positive) point
  rw [RFAP.IntegerPolynomialCertificate.eval_mul] at transported
  exact transported

end RFAP.FiniteCyclotomic
