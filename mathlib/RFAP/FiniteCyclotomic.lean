import mathlib.RFAP.FinitePolynomialExtensionality
import mathlib.RFAP.IntegerPolynomialCertificate
import mathlib.RFAP.ComputableDerivative
import mathlib.RFAP.CanonicalGCD
import mathlib.Tactic.QuotientFreeOmega

/-!
# Constructive finite cyclotomic factors

Ordinary cyclotomic factors are constructed here without roots of unity or
Mathlib's noncomputable cyclotomic hierarchy.  The coefficient program uses
the project's canonical rational records and finite dense long division.
The proof follows the elementary square-free divisor argument: previously
constructed pairwise-coprime factors all divide `X^n-1`, so their product
does too, and the next executable quotient is exact.
-/

namespace RFAP.FiniteCyclotomic

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Rational

open RFAP.ComputablePolynomial.DensePolynomial

/-- Pointwise equality is used only as an algebraic certificate.  Finite
coefficient extensionality converts it back to list equality whenever the
representation matters. -/
def EvalEq (left right : Polynomial) : Prop :=
  ∀ point : Rational, left.eval point = right.eval point

/-- Explicit polynomial divisibility, witnessed by one finite dense
quotient. -/
def EvalDvd (divisor dividend : Polynomial) : Prop :=
  ∃ quotient : Polynomial, EvalEq dividend (divisor * quotient)

/-- Explicit Bezout coprimality. -/
def EvalCoprime (left right : Polynomial) : Prop :=
  ∃ first second : Polynomial, ∀ point : Rational,
    1 = first.eval point * left.eval point +
      second.eval point * right.eval point

theorem evalEq_refl (polynomial : Polynomial) : EvalEq polynomial polynomial :=
  fun _ => rfl

theorem evalEq_symm {left right : Polynomial} (equal : EvalEq left right) :
    EvalEq right left := fun point => (equal point).symm

theorem evalEq_trans {first second third : Polynomial}
    (firstSecond : EvalEq first second) (secondThird : EvalEq second third) :
    EvalEq first third := fun point => (firstSecond point).trans (secondThird point)

theorem evalDvd_refl (polynomial : Polynomial) : EvalDvd polynomial polynomial := by
  refine ⟨constant 1, ?_⟩
  intro point
  rw [eval_mul, eval_constant, mul_one]

theorem evalDvd_trans {first second third : Polynomial}
    (firstSecond : EvalDvd first second) (secondThird : EvalDvd second third) :
    EvalDvd first third := by
  rcases firstSecond with ⟨firstFactor, firstIdentity⟩
  rcases secondThird with ⟨secondFactor, secondIdentity⟩
  refine ⟨firstFactor * secondFactor, ?_⟩
  intro point
  calc
    third.eval point = second.eval point * secondFactor.eval point := by
      simpa only [eval_mul] using secondIdentity point
    _ = (first.eval point * firstFactor.eval point) *
        secondFactor.eval point := by
      exact congrArg (fun value => value * secondFactor.eval point)
        (by simpa only [eval_mul] using firstIdentity point)
    _ = (first * (firstFactor * secondFactor)).eval point := by
      simp only [eval_mul]
      ring0

theorem evalDvd_mul_right (left right : Polynomial) :
    EvalDvd left (left * right) := ⟨right, evalEq_refl _⟩

theorem evalDvd_mul_left (left right : Polynomial) :
    EvalDvd right (left * right) := by
  refine ⟨left, ?_⟩
  intro point
  simp only [eval_mul]
  ring0

theorem evalCoprime_symm {left right : Polynomial}
    (coprime : EvalCoprime left right) : EvalCoprime right left := by
  rcases coprime with ⟨first, second, identity⟩
  refine ⟨second, first, ?_⟩
  intro point
  simpa only [add_comm] using identity point

theorem evalCoprime_one_left (polynomial : Polynomial) :
    EvalCoprime (constant 1) polynomial := by
  refine ⟨constant 1, 0, ?_⟩
  intro point
  simp only [eval_constant, eval_zero]
  ring0

theorem evalCoprime_one_right (polynomial : Polynomial) :
    EvalCoprime polynomial (constant 1) :=
  evalCoprime_symm (evalCoprime_one_left polynomial)

/-- Two coprimality certificates multiply on the left. -/
theorem evalCoprime_mul_left {first second third : Polynomial}
    (firstThird : EvalCoprime first third)
    (secondThird : EvalCoprime second third) :
    EvalCoprime (first * second) third := by
  rcases firstThird with ⟨a, b, firstIdentity⟩
  rcases secondThird with ⟨c, d, secondIdentity⟩
  refine ⟨a * c,
    a * d * first + b * c * second + b * d * third, ?_⟩
  intro point
  simp only [eval_mul, eval_add]
  calc
    1 = (a.eval point * first.eval point + b.eval point * third.eval point) *
          (c.eval point * second.eval point + d.eval point * third.eval point) := by
      rw [← firstIdentity point, ← secondIdentity point]
      ring0
    _ = (a.eval point * c.eval point) *
          (first.eval point * second.eval point) +
        (a.eval point * d.eval point * first.eval point +
            b.eval point * c.eval point * second.eval point +
            b.eval point * d.eval point * third.eval point) *
          third.eval point := by ring0

/-- Coprime divisors of the same polynomial may be multiplied. -/
theorem evalDvd_mul_of_coprime {first second dividend : Polynomial}
    (firstDivides : EvalDvd first dividend)
    (secondDivides : EvalDvd second dividend)
    (coprime : EvalCoprime first second) :
    EvalDvd (first * second) dividend := by
  rcases firstDivides with ⟨firstFactor, firstIdentity⟩
  rcases secondDivides with ⟨secondFactor, secondIdentity⟩
  rcases coprime with ⟨a, b, bezout⟩
  refine ⟨secondFactor * a + firstFactor * b, ?_⟩
  intro point
  simp only [eval_mul, eval_add]
  calc
    dividend.eval point = dividend.eval point * 1 := by ring0
    _ = dividend.eval point *
        (a.eval point * first.eval point +
          b.eval point * second.eval point) := by rw [← bezout point]
    _ = dividend.eval point * (a.eval point * first.eval point) +
        dividend.eval point * (b.eval point * second.eval point) := by ring0
    _ = (second.eval point * secondFactor.eval point) *
          (a.eval point * first.eval point) +
        (first.eval point * firstFactor.eval point) *
          (b.eval point * second.eval point) := by
      apply congrArg₂ (· + ·)
      · rw [secondIdentity point, eval_mul]
      · rw [firstIdentity point, eval_mul]
    _ = (first.eval point * second.eval point) *
        (secondFactor.eval point * a.eval point +
          firstFactor.eval point * b.eval point) := by ring0

/-- Product of an explicitly indexed finite family. -/
def productFin : (count : Nat) → (Fin count → Polynomial) → Polynomial
  | 0, _ => constant 1
  | count + 1, factor =>
      productFin count (fun index => factor index.castSucc) *
        factor (Fin.last count)

@[simp] theorem productFin_zero (factor : Fin 0 → Polynomial) :
    productFin 0 factor = constant 1 := rfl

@[simp] theorem productFin_succ (factor : Fin (count + 1) → Polynomial) :
    productFin (count + 1) factor =
      productFin count (fun index => factor index.castSucc) *
        factor (Fin.last count) := rfl

/-- Pointwise equality of a finite indexed family preserves its displayed
product, without converting the indexing functions themselves into equal
objects. -/
theorem productFin_congr : ∀ (count : Nat)
    (left right : Fin count → Polynomial),
    (∀ index, left index = right index) →
      productFin count left = productFin count right
  | 0, left, right, pointwise => rfl
  | count + 1, left, right, pointwise => by
      rw [productFin_succ, productFin_succ,
        productFin_congr count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc)
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]

theorem productFin_normalized : ∀ (count : Nat)
    (factor : Fin count → Polynomial),
    (productFin count factor).normalize = productFin count factor
  | 0, factor =>
      normalize_constant_of_ne RFAP.ConstructiveFraction.zero_ne_one.symm
  | count + 1, factor => by
      rw [productFin_succ, normalize_mul]

theorem productFin_nonzero : ∀ (count : Nat)
    (factor : Fin count → Polynomial),
    (∀ index, (factor index).isZero = false) →
    (productFin count factor).isZero = false
  | 0, factor, allNonzero => by
      exact isZero_false_of_eval_ne (x := 0) (by
        change (constant (1 : Rational)).eval 0 ≠ 0
        rw [eval_constant]
        exact RFAP.ConstructiveFraction.zero_ne_one.symm)
  | count + 1, factor, allNonzero => by
      rw [productFin_succ]
      exact isZero_mul_eq_false
        (productFin_nonzero count (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc))
        (allNonzero (Fin.last count))

theorem evalCoprime_productFin_left : ∀ (count : Nat)
    (factor : Fin count → Polynomial) (right : Polynomial),
    (∀ index, EvalCoprime (factor index) right) →
    EvalCoprime (productFin count factor) right
  | 0, factor, right, allCoprime => evalCoprime_one_left right
  | count + 1, factor, right, allCoprime => by
      rw [productFin_succ]
      exact evalCoprime_mul_left
        (evalCoprime_productFin_left count
          (fun index => factor index.castSucc) right
          (fun index => allCoprime index.castSucc))
        (allCoprime (Fin.last count))

theorem evalDvd_productFin_of_pairwise : ∀ (count : Nat)
    (factor : Fin count → Polynomial) (dividend : Polynomial),
    (∀ index, EvalDvd (factor index) dividend) →
    (∀ first second, first ≠ second →
      EvalCoprime (factor first) (factor second)) →
    EvalDvd (productFin count factor) dividend
  | 0, factor, dividend, allDivide, pairwise => by
      refine ⟨dividend, ?_⟩
      intro point
      simp only [productFin_zero, eval_mul, eval_constant, one_mul]
  | count + 1, factor, dividend, allDivide, pairwise => by
      rw [productFin_succ]
      apply evalDvd_mul_of_coprime
      · exact evalDvd_productFin_of_pairwise count
          (fun index => factor index.castSucc) dividend
          (fun index => allDivide index.castSucc)
          (fun first second different => pairwise first.castSucc second.castSucc
            (fun equal => by
              apply different
              apply Fin.ext
              exact congrArg (fun index : Fin (count + 1) => index.val) equal))
      · exact allDivide (Fin.last count)
      · apply evalCoprime_productFin_left
        intro index
        exact pairwise index.castSucc (Fin.last count)
          (fun equal => by
            have values := congrArg Fin.val equal
            simp only [Fin.val_castSucc, Fin.val_last] at values
            omega0)

/-- If one factor divides the left input of a Bezout certificate, it is also
coprime to the right input. -/
theorem evalCoprime_of_evalDvd_left {factor product right : Polynomial}
    (factorDivides : EvalDvd factor product)
    (coprime : EvalCoprime product right) : EvalCoprime factor right := by
  rcases factorDivides with ⟨cofactor, factorIdentity⟩
  rcases coprime with ⟨first, second, bezout⟩
  refine ⟨first * cofactor, second, ?_⟩
  intro point
  simp only [eval_mul]
  calc
    1 = first.eval point * product.eval point +
        second.eval point * right.eval point := bezout point
    _ = (first.eval point * cofactor.eval point) * factor.eval point +
        second.eval point * right.eval point := by
      rw [factorIdentity point, eval_mul]
      ring0

/-- Exact pointwise divisibility forces the executable long-division
remainder to be the represented zero. -/
theorem divMod_remainder_isZero_of_evalDvd
    (dividend divisor : Polynomial)
    (divisorNonzero : divisor.isZero = false)
    (divides : EvalDvd divisor dividend) :
    (divMod dividend divisor).remainder.isZero = true := by
  rcases divides with ⟨witness, witnessIdentity⟩
  let quotient := (divMod dividend divisor).quotient
  let remainder := (divMod dividend divisor).remainder
  let difference := witness - quotient
  have remainderIdentity : EvalEq remainder (divisor * difference) := by
    intro point
    have division := divMod_eval_equation dividend divisor point
    change remainder.eval point + divisor.eval point * quotient.eval point =
      dividend.eval point at division
    have witnessAt := witnessIdentity point
    rw [eval_mul] at witnessAt
    dsimp only [difference]
    rw [eval_mul, eval_sub]
    change remainder.eval point =
      divisor.eval point * (witness.eval point - quotient.eval point)
    calc
      remainder.eval point = dividend.eval point -
          divisor.eval point * quotient.eval point := by
        rw [← division]
        ring0
      _ = divisor.eval point * witness.eval point -
          divisor.eval point * quotient.eval point := by rw [witnessAt]
      _ = divisor.eval point *
          (witness.eval point - quotient.eval point) := by ring0
  have remainderNormalized : remainder.normalize = remainder := by
    exact divMod_remainder_normalize dividend divisor
  have productNormalized : (divisor * difference).normalize =
      divisor * difference := normalize_mul _ _
  have representedIdentity : remainder = divisor * difference :=
    RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
      remainderNormalized productNormalized remainderIdentity
  by_cases remainderZero : remainder.isZero = true
  · exact remainderZero
  · have remainderNonzero : remainder.isZero = false := by
      simpa using remainderZero
    have differenceNonzero : difference.isZero = false := by
      by_cases differenceZero : difference.isZero = true
      · have productZero : divisor * difference = 0 :=
          mul_eq_zero_of_isZero_right (p := divisor) differenceZero
        have remainderIsZero : remainder.isZero = true := by
          rw [representedIdentity, productZero, isZero_zero]
        rw [remainderIsZero] at remainderNonzero
        exact Bool.noConfusion remainderNonzero
      · simpa using differenceZero
    have productDegree := natDegree_mul divisorNonzero differenceNonzero
    have remainderDegreeBelow :=
      divMod_remainder_degreeCount_lt dividend divisor divisorNonzero
    change remainder.degreeCount < divisor.degreeCount at remainderDegreeBelow
    have remainderCount := natDegree_add_one_eq_degreeCount remainderNonzero
    have divisorCount := natDegree_add_one_eq_degreeCount divisorNonzero
    have degreeIdentity := congrArg
      (fun polynomial : Polynomial => polynomial.natDegree) representedIdentity
    rw [productDegree] at degreeIdentity
    omega0

/-- The monomial `X^degree`, built by finite repeated shifts. -/
def monomialOne : Nat → Polynomial
  | 0 => constant 1
  | degree + 1 => shift 1 (monomialOne degree)

@[simp] theorem monomialOne_zero : monomialOne 0 = constant 1 := rfl

@[simp] theorem monomialOne_succ (degree : Nat) :
    monomialOne (degree + 1) = shift 1 (monomialOne degree) := rfl

@[simp] theorem eval_monomialOne (degree : Nat) (point : Rational) :
    (monomialOne degree).eval point = point ^ degree := by
  induction degree with
  | zero => simp only [monomialOne_zero, eval_constant, pow_zero]
  | succ degree inductionHypothesis =>
      rw [monomialOne_succ, eval_shift, inductionHypothesis, pow_one,
        pow_succ]

theorem monomialOne_nonzero (degree : Nat) :
    (monomialOne degree).isZero = false :=
  isZero_false_of_eval_ne (x := 1) (by
    rw [eval_monomialOne, one_pow]
    exact RFAP.ConstructiveFraction.zero_ne_one.symm)

theorem monomialOne_normalized : ∀ degree : Nat,
    (monomialOne degree).normalize = monomialOne degree
  | 0 => normalize_constant_of_ne RFAP.ConstructiveFraction.zero_ne_one.symm
  | degree + 1 => by rw [monomialOne_succ, normalize_shift]

theorem monomialOne_coeffs : ∀ degree : Nat,
    (monomialOne degree).coeffs = 1 :: List.replicate degree 0
  | 0 => rfl
  | degree + 1 => by
      rw [monomialOne_succ, shift,
        if_neg (by simpa using monomialOne_nonzero degree),
        monomialOne_normalized, monomialOne_coeffs]
      apply congrArg (List.cons (1 : Rational))
      calc
        List.replicate degree (0 : Rational) ++ [0] =
            List.replicate degree 0 ++ List.replicate 1 0 := rfl
        _ = List.replicate (degree + 1) 0 :=
          (List.replicate_add degree 1 (0 : Rational)).symm

theorem monomialOne_natDegree (degree : Nat) :
    (monomialOne degree).natDegree = degree := by
  unfold natDegree degreeCount
  rw [monomialOne_normalized, monomialOne_coeffs]
  simp only [List.length_cons, List.length_replicate]
  omega0

theorem monomialOne_leadingCoeff (degree : Nat) :
    (monomialOne degree).leadingCoeff = 1 := by
  unfold leadingCoeff
  rw [monomialOne_normalized, monomialOne_coeffs]
  rfl

/-- The finite polynomial `X^degree-1`. -/
def powerMinusOne (degree : Nat) : Polynomial :=
  monomialOne degree - constant 1

@[simp] theorem eval_powerMinusOne (degree : Nat) (point : Rational) :
    (powerMinusOne degree).eval point = point ^ degree - 1 := by
  rw [powerMinusOne, eval_sub, eval_monomialOne, eval_constant]

theorem powerMinusOne_normalized (degree : Nat) :
    (powerMinusOne degree).normalize = powerMinusOne degree :=
  normalize_sub _ _

theorem powerMinusOne_coeffs (degree : Nat) :
    (powerMinusOne (degree + 1)).coeffs =
      (1 : Rational) :: List.replicate degree 0 ++ [(-1 : Rational)] := by
  unfold powerMinusOne
  change (add (monomialOne (degree + 1))
    (neg (constant 1))).coeffs = _
  have negConstant : neg (constant (1 : Rational)) = ⟨[-1]⟩ := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    change (-constant (1 : Rational) : Polynomial).coeffs = [-1]
    rw [neg_coeffs, normalize_constant_of_ne
      RFAP.ConstructiveFraction.zero_ne_one.symm]
    rfl
  rw [negConstant]
  unfold add
  rw [monomialOne_coeffs]
  unfold padLeft
  simp only [List.length_cons, List.length_replicate, List.length_nil,
    Nat.zero_add]
  have maximum : max (degree + 1 + 1) 1 = degree + 1 + 1 := by omega0
  rw [maximum]
  simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
  have padding : degree + 1 + 1 - 1 = degree + 1 := by omega0
  rw [padding, List.replicate_succ, List.cons_append,
    List.zipWith_cons_cons, add_zero]
  rw [normalize_coeffs]
  change
    ((1 : Rational) :: List.zipWith (· + ·)
      ((0 : Rational) :: List.replicate degree 0)
      (List.replicate degree 0 ++ [(-1 : Rational)])).dropWhile
        (· = 0) = _
  rw [List.dropWhile_cons_of_neg (by decide)]
  apply congrArg (List.cons 1)
  have zeroList :
      (0 : Rational) :: List.replicate degree 0 =
        List.replicate
          (List.replicate degree (0 : Rational) ++ [-1]).length 0 := by
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    rw [List.replicate_succ]
  rw [zeroList, zipWith_replicate_zero_add]
  rfl

theorem powerMinusOne_nonzero (degree : Nat) :
    (powerMinusOne (degree + 1)).isZero = false := by
  unfold isZero
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  rfl

theorem powerMinusOne_natDegree (degree : Nat) :
    (powerMinusOne (degree + 1)).natDegree = degree + 1 := by
  unfold natDegree degreeCount
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  simp only [List.length_cons, List.length_append, List.length_replicate,
    List.length_nil]
  omega0

theorem powerMinusOne_leadingCoeff (degree : Nat) :
    (powerMinusOne (degree + 1)).leadingCoeff = 1 := by
  unfold leadingCoeff
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  rfl

theorem eval_derivative_monomialOne : ∀ degree : Nat,
    ∀ point : Rational,
    (RFAP.ComputableDerivative.derivative (monomialOne degree)).eval point =
      (degree : Rational) * point ^ (degree - 1)
  | 0, point => by
      change (0 : Polynomial).eval point = (0 : Rational) * point ^ (0 - 1)
      simp only [eval_zero, zero_mul]
  | degree + 1, point => by
      rw [monomialOne_succ,
        RFAP.ComputableDerivative.eval_derivative_shift_one,
        eval_derivative_monomialOne degree point, eval_monomialOne]
      simp only [Nat.cast_add, Nat.cast_one]
      cases degree with
      | zero =>
          simp only [Nat.reduceSub, pow_zero]
          ring0
      | succ degree =>
          simp only [Nat.add_sub_cancel, pow_succ]
          ring0

theorem eval_derivative_powerMinusOne (degree : Nat) (point : Rational) :
    (RFAP.ComputableDerivative.derivative
      (powerMinusOne (degree + 1))).eval point =
      (degree + 1 : Nat) * point ^ degree := by
  rw [powerMinusOne, RFAP.ComputableDerivative.eval_derivative_sub,
    eval_derivative_monomialOne]
  change ((degree + 1 : Nat) : Rational) * point ^ (degree + 1 - 1) - 0 = _
  rw [Nat.add_sub_cancel]
  ring0

/-- `X^n-1` is square-free in the constructive rationals, with the explicit
Bezout certificate `-(X^n-1) + (X/n)(X^n-1)' = 1`. -/
theorem powerMinusOne_evalCoprime_derivative (degree : Nat) :
    EvalCoprime (powerMinusOne (degree + 1))
      (RFAP.ComputableDerivative.derivative
        (powerMinusOne (degree + 1))) := by
  let reciprocal : Rational := ((degree + 1 : Nat) : Rational)⁻¹
  refine ⟨constant (-1), scale reciprocal (monomialOne 1), ?_⟩
  intro point
  simp only [eval_constant, eval_scale, eval_monomialOne,
    eval_powerMinusOne, eval_derivative_powerMinusOne, pow_one]
  have degreeNonzero : (((degree + 1 : Nat) : Rational)) ≠ 0 := by
    intro zero
    have naturalZero := RFAP.ConstructiveFraction.natCast_injective_direct
      (zero.trans (Nat.cast_zero).symm)
    omega0
  have inverseCancel : reciprocal * (((degree + 1 : Nat) : Rational)) = 1 := by
    rw [mul_comm]
    exact RFAP.ExplicitField.mul_inv_cancel _ degreeNonzero
  symm
  change
    -1 * (point ^ (degree + 1) - 1) +
        (reciprocal * point) *
          (((degree + 1 : Nat) : Rational) * point ^ degree) = 1
  calc
    -1 * (point ^ (degree + 1) - 1) +
        (reciprocal * point) *
          (((degree + 1 : Nat) : Rational) * point ^ degree) =
      -(point ^ (degree + 1) - 1) +
        (reciprocal * (((degree + 1 : Nat) : Rational)) *
          point ^ (degree + 1)) := by
            rw [neg_one_mul, pow_succ]
            congr 1
            ring0
    _ = -(point ^ (degree + 1) - 1) + point ^ (degree + 1) := by
      rw [inverseCancel, one_mul]
    _ = 1 := by rw [neg_sub, sub_add_cancel]

/-- Two displayed factors of a square-free polynomial are explicitly
coprime. -/
theorem evalCoprime_factors_of_squarefree
    {whole left right : Polynomial}
    (wholeNormalized : whole.normalize = whole)
    (factorization : EvalEq whole (left * right))
    (squarefree : EvalCoprime whole
      (RFAP.ComputableDerivative.derivative whole)) :
    EvalCoprime left right := by
  have representedFactorization : whole = left * right :=
    RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
      wholeNormalized (normalize_mul _ _) factorization
  rcases squarefree with ⟨first, second, bezout⟩
  refine ⟨first * right + second *
      RFAP.ComputableDerivative.derivative right,
    second * RFAP.ComputableDerivative.derivative left, ?_⟩
  intro point
  simp only [eval_add, eval_mul]
  calc
    1 = first.eval point * whole.eval point + second.eval point *
        (RFAP.ComputableDerivative.derivative whole).eval point := bezout point
    _ = first.eval point * (left.eval point * right.eval point) +
        second.eval point *
          ((RFAP.ComputableDerivative.derivative left).eval point *
              right.eval point + left.eval point *
                (RFAP.ComputableDerivative.derivative right).eval point) := by
      rw [representedFactorization,
        RFAP.ComputableDerivative.eval_derivative_mul, eval_mul]
    _ = (first.eval point * right.eval point + second.eval point *
          (RFAP.ComputableDerivative.derivative right).eval point) *
        left.eval point +
      (second.eval point *
          (RFAP.ComputableDerivative.derivative left).eval point) *
        right.eval point := by ring0

/-- Finite geometric quotient in steps of one displayed exponent. -/
def geometricQuotient (step : Nat) : Nat → Polynomial
  | 0 => 0
  | count + 1 => geometricQuotient step count + monomialOne (count * step)

@[simp] theorem geometricQuotient_zero (step : Nat) :
    geometricQuotient step 0 = 0 := rfl

@[simp] theorem geometricQuotient_succ (step count : Nat) :
    geometricQuotient step (count + 1) =
      geometricQuotient step count + monomialOne (count * step) := rfl

theorem eval_geometricQuotient (step : Nat) : ∀ count : Nat,
    ∀ point : Rational,
    (geometricQuotient step count).eval point * (point ^ step - 1) =
      point ^ (count * step) - 1
  | 0, point => by
      simp only [geometricQuotient_zero, eval_zero, zero_mul, pow_zero]
      ring0
  | count + 1, point => by
      rw [geometricQuotient_succ, eval_add, eval_monomialOne,
        add_mul, eval_geometricQuotient step count point]
      rw [Nat.add_mul, Nat.one_mul, pow_add]
      ring0

/-- If `smaller` divides `larger` as positive exponents, then
`X^smaller-1` divides `X^larger-1` by a literal geometric sum. -/
theorem powerMinusOne_evalDvd_of_dvd {smaller larger : Nat}
    (divides : smaller ∣ larger) :
    EvalDvd (powerMinusOne smaller) (powerMinusOne larger) := by
  rcases divides with ⟨quotient, rfl⟩
  refine ⟨geometricQuotient smaller quotient, ?_⟩
  intro point
  simp only [eval_powerMinusOne, eval_mul]
  calc
    point ^ (smaller * quotient) - 1 =
        point ^ (quotient * smaller) - 1 := by rw [Nat.mul_comm]
    _ =
        (geometricQuotient smaller quotient).eval point *
          (point ^ smaller - 1) :=
      (eval_geometricQuotient smaller quotient point).symm
    _ = (point ^ smaller - 1) *
        (geometricQuotient smaller quotient).eval point := by ring0

/-- Executable long-division quotients stay normalized. -/
private theorem divLoop_quotient_normalized (fuel : Nat)
    (dividend divisor quotient : Polynomial)
    (quotientNormalized : quotient.normalize = quotient) :
    (divLoop fuel dividend divisor quotient).quotient.normalize =
      (divLoop fuel dividend divisor quotient).quotient := by
  induction fuel generalizing dividend quotient with
  | zero => exact quotientNormalized
  | succ fuel inductionHypothesis =>
      rw [divLoop_succ]
      split
      · exact quotientNormalized
      · dsimp only
        exact inductionHypothesis (cancelLead dividend divisor)
          (quotient + leadQuotient dividend divisor) (normalize_add _ _)

theorem divMod_quotient_normalized (dividend divisor : Polynomial) :
    (divMod dividend divisor).quotient.normalize =
      (divMod dividend divisor).quotient := by
  exact divLoop_quotient_normalized (dividend.degreeCount + 1)
    dividend.normalize divisor.normalize 0 normalize_zero

/-- Sum over an explicitly indexed finite natural family. -/
def sumFinNat : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, term =>
      sumFinNat count (fun index => term index.castSucc) + term (Fin.last count)

/-- Pointwise equality preserves the explicitly recursive finite sum. -/
theorem sumFinNat_congr : ∀ (count : Nat) (left right : Fin count → Nat),
    (∀ index, left index = right index) →
      sumFinNat count left = sumFinNat count right
  | 0, left, right, pointwise => rfl
  | count + 1, left, right, pointwise => by
      rw [sumFinNat, sumFinNat,
        sumFinNat_congr count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc)
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]

/-- The `Fin`-indexed implementation is the existing bounded natural sum
when its terms depend only on the displayed numeric label. -/
theorem sumFinNat_eq_finiteNatSum (count : Nat) (term : Nat → Nat) :
    sumFinNat count (fun index => term index.val) =
      RFAP.finiteNatSum count term := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [sumFinNat, RFAP.finiteNatSum_succ_last]
      change sumFinNat count (fun index => term index.val) + term count = _
      rw [inductionHypothesis]

/-- A bounded equality indicator carrying an arbitrary natural weight has
one contribution exactly when its target occurs in the displayed prefix. -/
theorem finiteNatSum_singletonWeight (count target weight : Nat) :
    RFAP.finiteNatSum count (fun index =>
        if RFAP.finiteNatEquals index target then weight else 0) =
      if RFAP.finiteNatLess target count then weight else 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [RFAP.finiteNatSum_succ_last, inductionHypothesis]
      by_cases targetBelow : target < count
      · have countDifferent : count ≠ target := by omega0
        rw [show RFAP.finiteNatLess target count = true by
              exact (RFAP.finiteNatLess_eq_true target count).2 targetBelow,
          show RFAP.finiteNatLess target (count + 1) = true by
              exact (RFAP.finiteNatLess_eq_true target (count + 1)).2 (by omega0),
          show RFAP.finiteNatEquals count target = false by
              exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
                countDifferent
                  ((RFAP.finiteNatEquals_eq_true count target).1 equal))]
        simp
      · by_cases targetEqual : target = count
        · subst target
          rw [show RFAP.finiteNatLess count count = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun below =>
                  (Nat.lt_irrefl count)
                    ((RFAP.finiteNatLess_eq_true count count).1 below)),
            show RFAP.finiteNatLess count (count + 1) = true by
                exact (RFAP.finiteNatLess_eq_true count (count + 1)).2 (by omega0),
            show RFAP.finiteNatEquals count count = true by
                exact (RFAP.finiteNatEquals_eq_true count count).2 rfl]
          simp
        · have targetAbove : count < target := by omega0
          rw [show RFAP.finiteNatLess target count = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun below =>
                  targetBelow
                    ((RFAP.finiteNatLess_eq_true target count).1 below)),
            show RFAP.finiteNatLess target (count + 1) = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun below =>
                  (by
                    have := (RFAP.finiteNatLess_eq_true
                      target (count + 1)).1 below
                    omega0)),
            show RFAP.finiteNatEquals count target = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
                  targetEqual
                    ((RFAP.finiteNatEquals_eq_true count target).1 equal).symm)]
          simp

/-- Pointwise splitting of a bounded natural sum into a `Fin`-indexed part
and an ordinary bounded part. -/
theorem finiteNatSum_eq_sumFinNat_add (count : Nat)
    (whole extra : Nat → Nat) (part : Fin count → Nat)
    (split : ∀ index : Fin count,
      whole index.val = part index + extra index.val) :
    RFAP.finiteNatSum count whole =
      sumFinNat count part + RFAP.finiteNatSum count extra := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [RFAP.finiteNatSum_succ_last, RFAP.finiteNatSum_succ_last,
        sumFinNat]
      rw [inductionHypothesis (fun index => part index.castSucc)
        (fun index => split index.castSucc)]
      have finalSplit := split (Fin.last count)
      simp only [Fin.val_last] at finalSplit
      omega0

/-- Degree of a nonzero finite product is the finite sum of degrees. -/
theorem natDegree_productFin : ∀ (count : Nat)
    (factor : Fin count → Polynomial),
    (∀ index, (factor index).isZero = false) →
    (productFin count factor).natDegree =
      sumFinNat count (fun index => (factor index).natDegree)
  | 0, factor, allNonzero => by
      simp only [productFin_zero, sumFinNat]
      rfl
  | count + 1, factor, allNonzero => by
      rw [productFin_succ, sumFinNat,
        natDegree_mul
          (productFin_nonzero count (fun index => factor index.castSucc)
            (fun index => allNonzero index.castSucc))
          (allNonzero (Fin.last count)),
        natDegree_productFin count (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc)]

/-- Subtracting exponents is literal Euclidean division for the special
polynomials `X^n-1`. -/
theorem powerMinusOne_subtraction_identity
    {smaller larger : Nat} (ordered : smaller ≤ larger) :
    EvalEq (powerMinusOne larger)
      (monomialOne (larger - smaller) * powerMinusOne smaller +
        powerMinusOne (larger - smaller)) := by
  intro point
  simp only [eval_powerMinusOne, eval_add, eval_mul, eval_monomialOne]
  have powerSplit : point ^ larger =
      point ^ (larger - smaller) * point ^ smaller := by
    calc
      point ^ larger = point ^ ((larger - smaller) + smaller) := by
        congr 1
        omega0
      _ = point ^ (larger - smaller) * point ^ smaller := pow_add _ _ _
  rw [powerSplit]
  ring0

/-- The finite subtraction algorithm gives explicit Bezout coefficients for
`X^m-1` and `X^n-1`.  Its exponent is the result of the project's certified,
structurally recursive Euclidean computation. -/
private theorem powerMinusOne_evalBezout_gcdAux :
    ∀ fuel first second : Nat, first + second < fuel →
      ∃ left right : Polynomial, ∀ point : Rational,
        (powerMinusOne (RFAP.CanonicalGCD.compute first second).gcd).eval point =
          left.eval point * (powerMinusOne first).eval point +
            right.eval point * (powerMinusOne second).eval point
  | 0, first, second, enoughFuel =>
      False.elim ((Nat.not_lt_zero _ ) enoughFuel)
  | fuel + 1, first, second, enoughFuel => by
      by_cases firstZero : first = 0
      · subst first
        refine ⟨0, constant 1, ?_⟩
        intro point
        rw [RFAP.CanonicalGCD.compute_gcd_zero_left]
        simp only [eval_zero, zero_mul, eval_constant, one_mul, zero_add]
      · by_cases secondZero : second = 0
        · subst second
          refine ⟨constant 1, 0, ?_⟩
          intro point
          rw [RFAP.CanonicalGCD.compute_gcd_zero_right]
          simp only [eval_constant, one_mul, eval_zero, zero_mul, add_zero]
        · by_cases ordered : first ≤ second
          · rcases powerMinusOne_evalBezout_gcdAux fuel first
                (second - first) (by omega0) with
              ⟨left, right, identity⟩
            refine ⟨left - right * monomialOne (second - first), right, ?_⟩
            intro point
            have split := powerMinusOne_subtraction_identity ordered point
            simp only [eval_add, eval_mul] at split
            have gcdStable :=
              RFAP.CanonicalGCD.compute_gcd_sub_right ordered
            simp only [eval_sub, eval_mul]
            calc
              (powerMinusOne
                  (RFAP.CanonicalGCD.compute first second).gcd).eval point =
                  (powerMinusOne
                    (RFAP.CanonicalGCD.compute first
                      (second - first)).gcd).eval point := by
                    rw [gcdStable]
              _ = left.eval point * (powerMinusOne first).eval point +
                    right.eval point *
                      (powerMinusOne (second - first)).eval point :=
                identity point
              _ = (left.eval point - right.eval point *
                      (monomialOne (second - first)).eval point) *
                    (powerMinusOne first).eval point +
                  right.eval point * (powerMinusOne second).eval point := by
                    rw [split]
                    ring0
          · have reverse : second ≤ first := Nat.le_of_not_ge ordered
            rcases powerMinusOne_evalBezout_gcdAux fuel (first - second)
                second (by omega0) with ⟨left, right, identity⟩
            refine ⟨left, right - left * monomialOne (first - second), ?_⟩
            intro point
            have split := powerMinusOne_subtraction_identity reverse point
            simp only [eval_add, eval_mul] at split
            have gcdStable :=
              RFAP.CanonicalGCD.compute_gcd_sub_left reverse
            simp only [eval_sub, eval_mul]
            calc
              (powerMinusOne
                  (RFAP.CanonicalGCD.compute first second).gcd).eval point =
                  (powerMinusOne
                    (RFAP.CanonicalGCD.compute (first - second)
                      second).gcd).eval point := by
                    rw [gcdStable]
              _ = left.eval point *
                    (powerMinusOne (first - second)).eval point +
                  right.eval point * (powerMinusOne second).eval point :=
                identity point
              _ = left.eval point * (powerMinusOne first).eval point +
                  (right.eval point - left.eval point *
                      (monomialOne (first - second)).eval point) *
                    (powerMinusOne second).eval point := by
                      rw [split]
                      ring0

/-- Public finite Bezout certificate for the two displayed exponents. -/
theorem powerMinusOne_evalBezout_gcd (first second : Nat) :
    ∃ left right : Polynomial, ∀ point : Rational,
      (powerMinusOne (RFAP.CanonicalGCD.compute first second).gcd).eval point =
        left.eval point * (powerMinusOne first).eval point +
          right.eval point * (powerMinusOne second).eval point :=
  powerMinusOne_evalBezout_gcdAux (first + second + 1) first second (by omega0)

/-- Fuelled implementation of the finite cyclotomic construction.  The
first argument is structural recursion fuel; the proof below shows that any
fuel strictly larger than the requested stage gives the same result. -/
def finiteCyclotomicAux : Nat → Nat → Polynomial
  | 0, _ => constant 1
  | _ + 1, 0 => constant 1
  | fuel + 1, number + 1 =>
      let properProduct := productFin (number + 2) fun divisor =>
        if _evidence : 2 ≤ divisor.val ∧ divisor.val ∣ number + 1 then
          finiteCyclotomicAux fuel ((number + 1) / divisor.val)
        else constant 1
      (divMod (powerMinusOne (number + 1)) properProduct).quotient

/-- Extra structural fuel does not change a stage once the fuel exceeds its
index. -/
theorem finiteCyclotomicAux_eq_of_enough_fuel : ∀ number : Nat,
    ∀ leftFuel rightFuel : Nat, number < leftFuel → number < rightFuel →
      finiteCyclotomicAux leftFuel number =
        finiteCyclotomicAux rightFuel number := by
  intro number
  induction number using Nat.strong_induction_on with
  | h number inductionHypothesis =>
      intro leftFuel rightFuel leftEnough rightEnough
      cases leftFuel with
      | zero => exact False.elim ((Nat.not_lt_zero _) leftEnough)
      | succ leftFuel =>
          cases rightFuel with
          | zero => exact False.elim ((Nat.not_lt_zero _) rightEnough)
          | succ rightFuel =>
              cases number with
              | zero => rfl
              | succ previous =>
                  rw [finiteCyclotomicAux, finiteCyclotomicAux]
                  apply congrArg fun product =>
                    (divMod (powerMinusOne (previous + 1)) product).quotient
                  apply productFin_congr
                  intro divisor
                  by_cases selected :
                      2 ≤ divisor.val ∧ divisor.val ∣ previous + 1
                  · rw [dif_pos selected, dif_pos selected]
                    have quotientProper :
                        (previous + 1) / divisor.val < previous + 1 :=
                      Nat.div_lt_self (by omega0) (by omega0)
                    apply inductionHypothesis _ quotientProper
                    · omega0
                    · omega0
                  · rw [dif_neg selected, dif_neg selected]

/-- Executable finite cyclotomic factor, evaluated with the least uniformly
sufficient structural fuel. -/
def finiteCyclotomic (number : Nat) : Polynomial :=
  finiteCyclotomicAux (number + 1) number

/-- One slot in the literal divisor-coordinate product at stage `number`. -/
def properCyclotomicFactor (number : Nat) (divisor : Fin (number + 1)) :
    Polynomial :=
    if _evidence : 2 ≤ divisor.val ∧ divisor.val ∣ number then
      finiteCyclotomic (number / divisor.val)
    else constant 1

/-- The literal product of all earlier divisor-indexed factors used to
construct `finiteCyclotomic number`. -/
def properCyclotomicProduct (number : Nat) : Polynomial :=
  productFin (number + 1) (properCyclotomicFactor number)

@[simp] theorem finiteCyclotomic_zero :
    finiteCyclotomic 0 = constant 1 := rfl

theorem finiteCyclotomic_succ (number : Nat) :
    finiteCyclotomic (number + 1) =
      (divMod (powerMinusOne (number + 1))
        (properCyclotomicProduct (number + 1))).quotient := by
  unfold finiteCyclotomic
  rw [finiteCyclotomicAux]
  unfold properCyclotomicProduct properCyclotomicFactor
  apply congrArg fun product =>
    (divMod (powerMinusOne (number + 1)) product).quotient
  apply productFin_congr
  intro divisor
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number + 1
  · rw [dif_pos selected, dif_pos selected]
    apply finiteCyclotomicAux_eq_of_enough_fuel
    · exact Nat.div_lt_self (by omega0) (by omega0)
    · omega0
  · rw [dif_neg selected, dif_neg selected]

/-- Every displayed slot divides its literal finite product. -/
theorem evalDvd_factor_productFin : ∀ (count : Nat)
    (factor : Fin count → Polynomial) (index : Fin count),
    EvalDvd (factor index) (productFin count factor)
  | 0, factor, index => Fin.elim0 index
  | count + 1, factor, index => by
      by_cases final : index.val = count
      · have indexLast : index = Fin.last count := Fin.ext final
        subst index
        rw [productFin_succ]
        exact evalDvd_mul_left _ _
      · have indexBelow : index.val < count := by
          have := index.isLt
          omega0
        let earlier : Fin count := ⟨index.val, indexBelow⟩
        apply evalDvd_trans
          (evalDvd_factor_productFin count
            (fun earlierIndex => factor earlierIndex.castSucc) earlier)
        exact evalDvd_mul_right _ _

theorem evalDvd_one (polynomial : Polynomial) :
    EvalDvd (constant 1) polynomial := by
  refine ⟨polynomial, ?_⟩
  intro point
  simp only [eval_mul, eval_constant, one_mul]

@[simp] theorem natDegree_constant_one :
    (constant (1 : Rational)).natDegree = 0 := by
  unfold natDegree degreeCount
  rw [normalize_constant_of_ne
    RFAP.ConstructiveFraction.zero_ne_one.symm]
  rfl

/-- Pointwise replacement of the represented divisor preserves explicit
divisibility. -/
theorem evalDvd_of_evalEq_divisor {first second dividend : Polynomial}
    (equal : EvalEq first second) (divides : EvalDvd second dividend) :
    EvalDvd first dividend := by
  rcases divides with ⟨quotient, identity⟩
  refine ⟨quotient, ?_⟩
  intro point
  rw [eval_mul, equal point]
  simpa only [eval_mul] using identity point

theorem evalDvd_right_of_factorization {whole left right : Polynomial}
    (factorization : EvalEq whole (left * right)) : EvalDvd right whole := by
  refine ⟨left, ?_⟩
  intro point
  calc
    whole.eval point = (left * right).eval point := factorization point
    _ = right.eval point * left.eval point := by
      simp only [eval_mul]
      ring0
    _ = (right * left).eval point := by rw [eval_mul]

theorem evalDvd_left_of_factorization {whole left right : Polynomial}
    (factorization : EvalEq whole (left * right)) : EvalDvd left whole := by
  refine ⟨right, factorization⟩

/-- A quotient coordinate of a divisor of a positive number is positive. -/
theorem divisorQuotient_positive {divisor number : Nat}
    (numberPositive : 0 < number) (divides : divisor ∣ number) :
    0 < number / divisor := by
  have reconstruction := Nat.div_mul_cancel divides
  by_contra quotientNotPositive
  have quotientZero : number / divisor = 0 :=
    Nat.eq_zero_of_not_pos quotientNotPositive
  rw [quotientZero, zero_mul] at reconstruction
  exact (Nat.ne_of_gt numberPositive) reconstruction.symm

theorem divisorQuotient_dvd {divisor number : Nat}
    (divides : divisor ∣ number) : number / divisor ∣ number := by
  refine ⟨divisor, ?_⟩
  exact (Nat.div_mul_cancel divides).symm

/-- A positive proper divisor has quotient coordinate at least two. -/
theorem divisorQuotient_two_le {divisor number : Nat}
    (divisorPositive : 0 < divisor) (divides : divisor ∣ number)
    (proper : divisor < number) : 2 ≤ number / divisor := by
  have reconstruction := Nat.div_mul_cancel divides
  by_contra belowTwo
  have quotientAtMostOne : number / divisor ≤ 1 := by omega0
  by_cases quotientZero : number / divisor = 0
  · rw [quotientZero, zero_mul] at reconstruction
    omega0
  · have quotientPositive : 0 < number / divisor :=
      Nat.pos_of_ne_zero quotientZero
    have quotientOne : number / divisor = 1 := by omega0
    rw [quotientOne, one_mul] at reconstruction
    omega0

/-- Dividing by the complementary coordinate recovers a positive divisor. -/
theorem divide_by_divisorQuotient {divisor number : Nat}
    (numberPositive : 0 < number) (divides : divisor ∣ number) :
    number / (number / divisor) = divisor := by
  have reconstruction : number / divisor * divisor = number :=
    Nat.div_mul_cancel divides
  have quotientPositive : 0 < number / divisor := by
    by_contra quotientNotPositive
    have quotientZero : number / divisor = 0 :=
      Nat.eq_zero_of_not_pos quotientNotPositive
    rw [quotientZero, zero_mul] at reconstruction
    exact (Nat.ne_of_gt numberPositive) reconstruction.symm
  have quotientDivides : number / divisor ∣ number := by
    refine ⟨divisor, ?_⟩
    exact reconstruction.symm
  have secondReconstruction := Nat.div_mul_cancel quotientDivides
  apply Nat.eq_of_mul_eq_mul_right quotientPositive
  calc
    number / (number / divisor) * (number / divisor) = number :=
      secondReconstruction
    _ = divisor * (number / divisor) := by
      rw [mul_comm]
      exact reconstruction.symm

/-- Every earlier positive divisor factor occurs in the later stage's
literal quotient-coordinate product. -/
theorem finiteCyclotomic_evalDvd_properProduct
    {divisor number : Nat} (divisorPositive : 0 < divisor)
    (divides : divisor ∣ number) (proper : divisor < number) :
    EvalDvd (finiteCyclotomic divisor)
      (properCyclotomicProduct number) := by
  let coordinate : Fin (number + 1) :=
    ⟨number / divisor, Nat.lt_succ_of_le (Nat.div_le_self _ _)⟩
  have coordinateDivides : coordinate.val ∣ number := by
    refine ⟨divisor, ?_⟩
    dsimp only [coordinate]
    exact (Nat.div_mul_cancel divides).symm
  have coordinateLarge : 2 ≤ coordinate.val := by
    exact divisorQuotient_two_le divisorPositive divides proper
  have selected : properCyclotomicFactor number coordinate =
      finiteCyclotomic divisor := by
    unfold properCyclotomicFactor
    rw [dif_pos ⟨coordinateLarge, coordinateDivides⟩]
    congr 1
    exact divide_by_divisorQuotient (by omega0) divides
  rw [properCyclotomicProduct]
  rw [← selected]
  exact evalDvd_factor_productFin (number + 1)
    (properCyclotomicFactor number) coordinate

/-- The simultaneous induction invariant for the finite construction. -/
structure StageSpec (number : Nat) : Prop where
  normalized : (finiteCyclotomic number).normalize = finiteCyclotomic number
  nonzero : (finiteCyclotomic number).isZero = false
  factorization : EvalEq (powerMinusOne number)
    (properCyclotomicProduct number * finiteCyclotomic number)
  properCoprime : EvalCoprime (properCyclotomicProduct number)
    (finiteCyclotomic number)
  earlierCoprime : ∀ earlier : Nat, 0 < earlier → earlier < number →
    EvalCoprime (finiteCyclotomic earlier) (finiteCyclotomic number)

/-- Every positive stage of the executable construction is exact, nonzero,
and coprime to all earlier stages. -/
theorem finiteCyclotomic_stageSpec :
    ∀ number : Nat, 0 < number → StageSpec number
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have quotientPositive (stage : Nat) (stagePositive : 0 < stage)
          (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          0 < stage / index.val :=
        divisorQuotient_positive stagePositive selected.2
      have quotientProper (stage : Nat) (stagePositive : 0 < stage)
          (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          stage / index.val < stage :=
        Nat.div_lt_self stagePositive (by omega0)
      have quotientDivides (stage : Nat) (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          stage / index.val ∣ stage :=
        divisorQuotient_dvd selected.2
      have factorNormalized (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1)
          (index : Fin (stage + 1)) :
          (properCyclotomicFactor stage index).normalize =
            properCyclotomicFactor stage index := by
        by_cases selected : 2 ≤ index.val ∧ index.val ∣ stage
        · rw [properCyclotomicFactor, dif_pos selected]
          have quotientLt := quotientProper stage stagePositive index selected
          exact (finiteCyclotomic_stageSpec (stage / index.val)
            (quotientPositive stage stagePositive index selected)).normalized
        · rw [properCyclotomicFactor, dif_neg selected]
          exact normalize_constant_of_ne
            RFAP.ConstructiveFraction.zero_ne_one.symm
      have factorNonzero (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1)
          (index : Fin (stage + 1)) :
          (properCyclotomicFactor stage index).isZero = false := by
        by_cases selected : 2 ≤ index.val ∧ index.val ∣ stage
        · rw [properCyclotomicFactor, dif_pos selected]
          have quotientLt := quotientProper stage stagePositive index selected
          exact (finiteCyclotomic_stageSpec (stage / index.val)
            (quotientPositive stage stagePositive index selected)).nonzero
        · rw [properCyclotomicFactor, dif_neg selected]
          exact isZero_false_of_eval_ne (x := 0) (by
            rw [eval_constant]
            exact RFAP.ConstructiveFraction.zero_ne_one.symm)
      have factorsPairwise (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1) :
          ∀ first second : Fin (stage + 1), first ≠ second →
            EvalCoprime (properCyclotomicFactor stage first)
              (properCyclotomicFactor stage second) := by
        intro first second different
        by_cases firstSelected :
            2 ≤ first.val ∧ first.val ∣ stage
        · by_cases secondSelected :
              2 ≤ second.val ∧ second.val ∣ stage
          · rw [properCyclotomicFactor, dif_pos firstSelected,
              properCyclotomicFactor, dif_pos secondSelected]
            have firstPositive := quotientPositive stage stagePositive
              first firstSelected
            have secondPositive := quotientPositive stage stagePositive
              second secondSelected
            have firstProper := quotientProper stage stagePositive
              first firstSelected
            have secondProper := quotientProper stage stagePositive
              second secondSelected
            have quotientDifferent : stage / first.val ≠
                stage / second.val := by
              intro quotientEqual
              apply different
              apply Fin.ext
              apply Nat.eq_of_mul_eq_mul_left firstPositive
              calc
                stage / first.val * first.val = stage :=
                  Nat.div_mul_cancel firstSelected.2
                _ = stage / second.val * second.val :=
                  (Nat.div_mul_cancel secondSelected.2).symm
                _ = stage / first.val * second.val := by
                  rw [quotientEqual]
            by_cases ordered : stage / first.val < stage / second.val
            · exact (finiteCyclotomic_stageSpec (stage / second.val)
                secondPositive).earlierCoprime (stage / first.val)
                  firstPositive ordered
            · have reverse : stage / second.val < stage / first.val := by
                omega0
              exact evalCoprime_symm
                ((finiteCyclotomic_stageSpec (stage / first.val)
                  firstPositive).earlierCoprime (stage / second.val)
                    secondPositive reverse)
          · rw [properCyclotomicFactor, dif_pos firstSelected,
              properCyclotomicFactor, dif_neg secondSelected]
            exact evalCoprime_one_right _
        · by_cases secondSelected :
              2 ≤ second.val ∧ second.val ∣ stage
          · rw [properCyclotomicFactor, dif_neg firstSelected,
              properCyclotomicFactor, dif_pos secondSelected]
            exact evalCoprime_one_left _
          · rw [properCyclotomicFactor, dif_neg firstSelected,
              properCyclotomicFactor, dif_neg secondSelected]
            exact evalCoprime_one_left _
      have factorsDividePower : ∀ index : Fin (previous + 2),
          EvalDvd (properCyclotomicFactor (previous + 1) index)
            (powerMinusOne (previous + 1)) := by
        intro index
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [properCyclotomicFactor, dif_pos selected]
          let quotient := (previous + 1) / index.val
          have quotientPos : 0 < quotient :=
            quotientPositive (previous + 1) positive index selected
          have quotientLt : quotient < previous + 1 :=
            quotientProper (previous + 1) positive index selected
          have quotientDvd : quotient ∣ previous + 1 :=
            quotientDivides (previous + 1) index selected
          apply evalDvd_trans
            (evalDvd_right_of_factorization
              (finiteCyclotomic_stageSpec quotient quotientPos).factorization)
          exact powerMinusOne_evalDvd_of_dvd quotientDvd
        · rw [properCyclotomicFactor, dif_neg selected]
          exact evalDvd_one _
      have properDividesPower :
          EvalDvd (properCyclotomicProduct (previous + 1))
            (powerMinusOne (previous + 1)) := by
        rw [properCyclotomicProduct]
        exact evalDvd_productFin_of_pairwise (previous + 2)
          (properCyclotomicFactor (previous + 1))
          (powerMinusOne (previous + 1)) factorsDividePower
          (factorsPairwise (previous + 1) positive (Nat.le_refl _))
      have properNonzero :
          (properCyclotomicProduct (previous + 1)).isZero = false := by
        rw [properCyclotomicProduct]
        exact productFin_nonzero (previous + 2)
          (properCyclotomicFactor (previous + 1))
          (factorNonzero (previous + 1) positive (Nat.le_refl _))
      have remainderZero :
          (divMod (powerMinusOne (previous + 1))
            (properCyclotomicProduct (previous + 1))).remainder.isZero = true :=
        divMod_remainder_isZero_of_evalDvd _ _ properNonzero
          properDividesPower
      have factorization : EvalEq (powerMinusOne (previous + 1))
          (properCyclotomicProduct (previous + 1) *
            finiteCyclotomic (previous + 1)) := by
        intro point
        have division := divMod_eval_equation
          (powerMinusOne (previous + 1))
          (properCyclotomicProduct (previous + 1)) point
        have remainderAtPoint := eval_eq_zero_of_isZero remainderZero point
        rw [remainderAtPoint, zero_add] at division
        rw [finiteCyclotomic_succ, eval_mul]
        exact division.symm
      have cyclotomicNonzero :
          (finiteCyclotomic (previous + 1)).isZero = false := by
        by_cases zero : (finiteCyclotomic (previous + 1)).isZero = true
        · have zeroAtPoint := eval_eq_zero_of_isZero zero (0 : Rational)
          have identity := factorization (0 : Rational)
          rw [eval_powerMinusOne, zero_pow (by omega0), eval_mul,
            zeroAtPoint, mul_zero] at identity
          have oneZero : (1 : Rational) = 0 := by
            calc
              1 = -(-1 : Rational) := by ring0
              _ = -0 := congrArg Neg.neg identity
              _ = 0 := by ring0
          exact (RFAP.ConstructiveFraction.zero_ne_one oneZero.symm).elim
        · simpa using zero
      have properCoprime : EvalCoprime
          (properCyclotomicProduct (previous + 1))
          (finiteCyclotomic (previous + 1)) :=
        evalCoprime_factors_of_squarefree
          (powerMinusOne_normalized (previous + 1)) factorization
          (powerMinusOne_evalCoprime_derivative previous)
      have properProductDivides (divisor : Nat) (divisorPositive : 0 < divisor)
          (divisorProper : divisor < previous + 1)
          (divisorDivides : divisor ∣ previous + 1) :
          EvalDvd (properCyclotomicProduct divisor)
            (properCyclotomicProduct (previous + 1)) := by
        rw [properCyclotomicProduct]
        apply evalDvd_productFin_of_pairwise
        · intro index
          by_cases selected :
              2 ≤ index.val ∧ index.val ∣ divisor
          · rw [properCyclotomicFactor, dif_pos selected]
            have quotientPos := quotientPositive divisor divisorPositive
              index selected
            have quotientDvdDivisor := quotientDivides divisor index selected
            have quotientDvdCurrent :=
              Nat.dvd_trans quotientDvdDivisor divisorDivides
            have quotientLtDivisor := quotientProper divisor divisorPositive
              index selected
            exact finiteCyclotomic_evalDvd_properProduct quotientPos
              quotientDvdCurrent (by omega0)
          · rw [properCyclotomicFactor, dif_neg selected]
            exact evalDvd_one _
        · exact factorsPairwise divisor divisorPositive
            (Nat.le_of_lt divisorProper)
      have earlierCoprime : ∀ earlier : Nat, 0 < earlier →
          earlier < previous + 1 →
          EvalCoprime (finiteCyclotomic earlier)
            (finiteCyclotomic (previous + 1)) := by
        intro earlier earlierPositive earlierProper
        let common :=
          (RFAP.CanonicalGCD.compute earlier (previous + 1)).gcd
        have commonPositive : 0 < common := by
          exact RFAP.CanonicalGCD.compute_gcd_positive_right earlier positive
        have commonDividesCurrent : common ∣ previous + 1 := by
          exact (RFAP.CanonicalGCD.compute_spec earlier (previous + 1)).2.2
        have commonAtMostEarlier : common ≤ earlier := by
          exact Nat.le_of_dvd earlierPositive
            (RFAP.CanonicalGCD.compute_spec earlier (previous + 1)).2.1
        have commonProper : common < previous + 1 := by omega0
        have commonStage := finiteCyclotomic_stageSpec common commonPositive
        have commonProperProductDivides := properProductDivides common
          commonPositive commonProper commonDividesCurrent
        have commonCyclotomicDivides :=
          finiteCyclotomic_evalDvd_properProduct commonPositive
            commonDividesCurrent commonProper
        have representedCommonDivides : EvalDvd
            (properCyclotomicProduct common * finiteCyclotomic common)
            (properCyclotomicProduct (previous + 1)) :=
          evalDvd_mul_of_coprime commonProperProductDivides
            commonCyclotomicDivides commonStage.properCoprime
        have commonPowerDivides : EvalDvd (powerMinusOne common)
            (properCyclotomicProduct (previous + 1)) :=
          evalDvd_of_evalEq_divisor commonStage.factorization
            representedCommonDivides
        have commonPowerCoprime : EvalCoprime (powerMinusOne common)
            (finiteCyclotomic (previous + 1)) :=
          evalCoprime_of_evalDvd_left commonPowerDivides properCoprime
        rcases powerMinusOne_evalBezout_gcd earlier (previous + 1) with
          ⟨gcdLeft, gcdRight, gcdIdentity⟩
        rcases commonPowerCoprime with
          ⟨commonLeft, cyclotomicRight, commonIdentity⟩
        have earlierPowerCoprime : EvalCoprime (powerMinusOne earlier)
            (finiteCyclotomic (previous + 1)) := by
          refine ⟨commonLeft * gcdLeft,
            commonLeft * gcdRight * properCyclotomicProduct (previous + 1) +
              cyclotomicRight, ?_⟩
          intro point
          simp only [eval_mul, eval_add]
          have gcdAtPoint := gcdIdentity point
          change (powerMinusOne common).eval point = _ at gcdAtPoint
          calc
            1 = commonLeft.eval point * (powerMinusOne common).eval point +
                cyclotomicRight.eval point *
                  (finiteCyclotomic (previous + 1)).eval point :=
              commonIdentity point
            _ = commonLeft.eval point *
                  (gcdLeft.eval point * (powerMinusOne earlier).eval point +
                    gcdRight.eval point *
                      (powerMinusOne (previous + 1)).eval point) +
                cyclotomicRight.eval point *
                  (finiteCyclotomic (previous + 1)).eval point := by
                    rw [gcdAtPoint]
            _ = (commonLeft.eval point * gcdLeft.eval point) *
                  (powerMinusOne earlier).eval point +
                (commonLeft.eval point * gcdRight.eval point *
                    (properCyclotomicProduct (previous + 1)).eval point +
                  cyclotomicRight.eval point) *
                    (finiteCyclotomic (previous + 1)).eval point := by
                      rw [factorization point, eval_mul]
                      ring0
        exact evalCoprime_of_evalDvd_left
          (evalDvd_right_of_factorization
            (finiteCyclotomic_stageSpec earlier earlierPositive).factorization)
          earlierPowerCoprime
      exact
        { normalized := by
            rw [finiteCyclotomic_succ]
            exact divMod_quotient_normalized _ _
          nonzero := cyclotomicNonzero
          factorization := factorization
          properCoprime := properCoprime
          earlierCoprime := earlierCoprime }
termination_by number => number
decreasing_by all_goals omega0

theorem properCyclotomicFactor_nonzero (number : Nat)
    (positive : 0 < number) (index : Fin (number + 1)) :
    (properCyclotomicFactor number index).isZero = false := by
  by_cases selected : 2 ≤ index.val ∧ index.val ∣ number
  · rw [properCyclotomicFactor, dif_pos selected]
    exact (finiteCyclotomic_stageSpec (number / index.val)
      (divisorQuotient_positive positive selected.2)).nonzero
  · rw [properCyclotomicFactor, dif_neg selected]
    exact isZero_false_of_eval_ne (x := 0) (by
      rw [eval_constant]
      exact RFAP.ConstructiveFraction.zero_ne_one.symm)

theorem properCyclotomicProduct_nonzero (number : Nat)
    (positive : 0 < number) :
    (properCyclotomicProduct number).isZero = false := by
  rw [properCyclotomicProduct]
  exact productFin_nonzero (number + 1) (properCyclotomicFactor number)
    (properCyclotomicFactor_nonzero number positive)

/-- The executable quotient at positive index `n` has exactly the finite
Euler-totient degree. -/
theorem finiteCyclotomic_natDegree : ∀ number : Nat, 0 < number →
    (finiteCyclotomic number).natDegree = RFAP.finiteTotient number
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have termSplit (index : Fin (previous + 2)) :
          (if RFAP.finiteDivides index.val (previous + 1) then
              RFAP.finiteTotient ((previous + 1) / index.val) else 0) =
            (properCyclotomicFactor (previous + 1) index).natDegree +
              (if RFAP.finiteNatEquals index.val 1 then
                RFAP.finiteTotient (previous + 1) else 0) := by
        by_cases divides : index.val ∣ previous + 1
        · rw [show RFAP.finiteDivides index.val (previous + 1) = true by
              exact (RFAP.finiteDivides_eq_true _ _).2 divides]
          by_cases large : 2 ≤ index.val
          · have selected : 2 ≤ index.val ∧ index.val ∣ previous + 1 :=
              ⟨large, divides⟩
            have indexNotOne : index.val ≠ 1 := by omega0
            rw [if_pos rfl, properCyclotomicFactor, dif_pos selected,
              finiteCyclotomic_natDegree ((previous + 1) / index.val)
                (divisorQuotient_positive positive divides),
              show RFAP.finiteNatEquals index.val 1 = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
                  indexNotOne
                    ((RFAP.finiteNatEquals_eq_true index.val 1).1 equal)),
              if_neg (by decide), Nat.add_zero]
            omega0
          · have indexPositive : 0 < index.val := by
              by_contra notPositive
              have indexZero : index.val = 0 :=
                Nat.eq_zero_of_not_pos notPositive
              have zeroDivides : 0 ∣ previous + 1 := by
                rw [← indexZero]
                exact divides
              have currentZero := Nat.eq_zero_of_zero_dvd zeroDivides
              omega0
            have indexOne : index.val = 1 := by omega0
            have notSelected : ¬(2 ≤ index.val ∧
                index.val ∣ previous + 1) := by omega0
            rw [if_pos rfl, properCyclotomicFactor, dif_neg notSelected,
              indexOne, Nat.div_one,
              show RFAP.finiteNatEquals 1 1 = true by
                exact (RFAP.finiteNatEquals_eq_true 1 1).2 rfl,
              if_pos rfl]
            rw [natDegree_constant_one, Nat.zero_add]
        · have notSelected : ¬(2 ≤ index.val ∧
              index.val ∣ previous + 1) := fun selected =>
                divides selected.2
          have indexNotOne : index.val ≠ 1 := by
            intro indexOne
            apply divides
            rw [indexOne]
            exact one_dvd _
          rw [show RFAP.finiteDivides index.val (previous + 1) = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun truth =>
                  divides ((RFAP.finiteDivides_eq_true _ _).1 truth)),
            if_neg (by decide), properCyclotomicFactor, dif_neg notSelected,
            show RFAP.finiteNatEquals index.val 1 = false by
                exact RFAP.finiteBool_eq_false_of_not_eq_true _ (fun equal =>
                  indexNotOne
                    ((RFAP.finiteNatEquals_eq_true index.val 1).1 equal)),
            if_neg (by decide)]
          rw [natDegree_constant_one, Nat.zero_add]
      have divisorSumSplit :
          RFAP.finiteDivisorQuotientTotientSum (previous + 1) =
            sumFinNat (previous + 2) (fun index =>
              (properCyclotomicFactor (previous + 1) index).natDegree) +
              RFAP.finiteTotient (previous + 1) := by
        unfold RFAP.finiteDivisorQuotientTotientSum
        calc
          RFAP.finiteNatSum (previous + 2) (fun divisor =>
              if RFAP.finiteDivides divisor (previous + 1) then
                RFAP.finiteTotient ((previous + 1) / divisor) else 0) =
            sumFinNat (previous + 2) (fun index =>
                (properCyclotomicFactor (previous + 1) index).natDegree) +
              RFAP.finiteNatSum (previous + 2) (fun divisor =>
                if RFAP.finiteNatEquals divisor 1 then
                  RFAP.finiteTotient (previous + 1) else 0) :=
              finiteNatSum_eq_sumFinNat_add _ _ _ _ termSplit
          _ = sumFinNat (previous + 2) (fun index =>
                (properCyclotomicFactor (previous + 1) index).natDegree) +
              RFAP.finiteTotient (previous + 1) := by
                rw [finiteNatSum_singletonWeight]
                rw [show RFAP.finiteNatLess 1 (previous + 2) = true by
                  exact (RFAP.finiteNatLess_eq_true 1 (previous + 2)).2
                    (by omega0)]
                simp
      have properDegree :
          (properCyclotomicProduct (previous + 1)).natDegree =
            sumFinNat (previous + 2) (fun index =>
              (properCyclotomicFactor (previous + 1) index).natDegree) := by
        rw [properCyclotomicProduct]
        exact natDegree_productFin (previous + 2)
          (properCyclotomicFactor (previous + 1))
          (properCyclotomicFactor_nonzero (previous + 1) positive)
      have stage := finiteCyclotomic_stageSpec (previous + 1) positive
      have representedFactorization : powerMinusOne (previous + 1) =
          properCyclotomicProduct (previous + 1) *
            finiteCyclotomic (previous + 1) :=
        RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
          (powerMinusOne_normalized (previous + 1)) (normalize_mul _ _)
          stage.factorization
      have degreeIdentity := congrArg
        (fun polynomial : Polynomial => polynomial.natDegree)
        representedFactorization
      rw [powerMinusOne_natDegree previous,
        natDegree_mul (properCyclotomicProduct_nonzero (previous + 1) positive)
          stage.nonzero,
        properDegree] at degreeIdentity
      have divisorDegreeTotal :=
        RFAP.finiteDivisorQuotientTotientSum_eq (previous + 1)
      rw [divisorSumSplit] at divisorDegreeTotal
      omega0
termination_by number => number
decreasing_by all_goals
  exact Nat.div_lt_self (by omega0) (by omega0)

end RFAP.FiniteCyclotomic
