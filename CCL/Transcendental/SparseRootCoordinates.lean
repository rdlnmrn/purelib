import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructivePolynomialLeading
import mathlib.RFAP.ConstructiveRationalRootCandidates

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

namespace CCL.SparseRootCoordinates

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading
open RFAP.ConstructiveGaussian.Gaussian

/-- A normalized rational constant, including the zero branch. -/
def normalizedConstant (value : Coordinate) : Polynomial :=
  if value = 0 then 0 else constant value

@[simp] theorem eval_normalizedConstant (value point : Coordinate) :
    (normalizedConstant value).eval point = value := by
  rw [normalizedConstant]
  split
  · rename_i zero
    rw [zero, eval_zero]
  · exact eval_constant value point

theorem normalizedConstant_atMost (value : Coordinate) :
    DegreeAtMost (normalizedConstant value) 0 := by
  by_cases zero : value = 0
  · rw [normalizedConstant, if_pos zero]
    exact DegreeAtMost.zero 0
  · rw [normalizedConstant, if_neg zero]
    exact (LeadingTerm.constant zero).atMost

/-- The polynomial `2X`. -/
def twiceVariable : Polynomial := ⟨[2, 0]⟩

@[simp] theorem eval_twiceVariable (point : Coordinate) :
    twiceVariable.eval point = 2 * point := by
  change (0 * point + 2) * point + 0 = 2 * point
  ring1

theorem twiceVariable_leading : LeadingTerm twiceVariable 1 2 := by
  have twoNonzero : (2 : Coordinate) ≠ 0 := by decide
  refine
    { normalized := ?_
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    change ([2, 0] : List Coordinate).dropWhile (· = 0) = [2, 0]
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
  · change (([2, 0] : List Coordinate).dropWhile (· = 0)).isEmpty = false
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl
  · change (([2, 0] : List Coordinate).dropWhile (· = 0)).length - 1 = 1
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl
  · change (([2, 0] : List Coordinate).dropWhile (· = 0)).headD 0 = 2
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl

/-- Consecutive Lucas polynomials `(A_n,A_{n+1})` at one displayed radius. -/
def tracePair (radius : Coordinate) : Nat → Polynomial × Polynomial
  | 0 => (normalizedConstant 2, twiceVariable)
  | index + 1 =>
      let previous := tracePair radius index
      (previous.2,
        twiceVariable * previous.2 -
          normalizedConstant radius * previous.1)

/-- The finite Lucas coordinate polynomial `A_n(X,radius)`. -/
def tracePolynomial (radius : Coordinate) (degree : Nat) : Polynomial :=
  (tracePair radius degree).1

/-- The recurrence step exposed without the implementation pair. -/
theorem tracePolynomial_succ_succ (radius : Coordinate) (degree : Nat) :
    tracePolynomial radius (degree + 2) =
      twiceVariable * tracePolynomial radius (degree + 1) -
        normalizedConstant radius * tracePolynomial radius degree := by
  rfl

@[simp] theorem tracePolynomial_zero (radius : Coordinate) :
    tracePolynomial radius 0 = normalizedConstant 2 := rfl

@[simp] theorem tracePolynomial_one (radius : Coordinate) :
    tracePolynomial radius 1 = twiceVariable := rfl

theorem tracePair_shape (radius : Coordinate) : ∀ degree,
    DegreeAtMost (tracePair radius degree).1 degree ∧
      LeadingTerm (tracePair radius degree).2 (degree + 1)
        (2 ^ (degree + 1)) := by
  intro degree
  induction degree with
  | zero =>
      constructor
      · exact normalizedConstant_atMost 2
      · exact LeadingTerm.of_equal rfl rfl
          (by rw [Nat.zero_add, pow_one]) twiceVariable_leading
  | succ degree inductionHypothesis =>
      rw [tracePair]
      let previous := tracePair radius degree
      constructor
      · exact inductionHypothesis.2.atMost
      have firstLeading :
          LeadingTerm (twiceVariable * previous.2) (degree + 2)
            (2 * 2 ^ (degree + 1)) := by
        have multiplied :=
          LeadingTerm.mul twiceVariable_leading inductionHypothesis.2
        exact LeadingTerm.of_equal rfl
          (by rw [Nat.one_add]) rfl multiplied
      have previousFirstAtMost :
          DegreeAtMost previous.1 degree := inductionHypothesis.1
      have radiusAtMost : DegreeAtMost (normalizedConstant radius) 0 :=
        normalizedConstant_atMost radius
      have lowerBelow :
          DegreeBelow (normalizedConstant radius * previous.1)
            (degree + 2) := by
        have below :=
          (DegreeAtMost.mul radiusAtMost previousFirstAtMost).toBelowSucc
        exact below.mono (by
          calc
            0 + degree + 1 = degree + 1 := by rw [Nat.zero_add]
            _ ≤ degree + 2 := Nat.le_succ (degree + 1))
      have result := firstLeading.subBelow lowerBelow
      change LeadingTerm
        (twiceVariable * previous.2 - normalizedConstant radius * previous.1)
        (Nat.succ degree + 1) (2 ^ (Nat.succ degree + 1))
      have coefficientIdentity :
          (2 : Coordinate) * 2 ^ (degree + 1) = 2 ^ (degree + 2) := by
        rw [pow_succ]
        ring1
      exact LeadingTerm.of_equal rfl rfl coefficientIdentity.symm result

theorem tracePair_leading (radius : Coordinate) (degree : Nat) :
    LeadingTerm (tracePair radius degree).2 (degree + 1)
      (2 ^ (degree + 1)) :=
  (tracePair_shape radius degree).2

theorem tracePolynomial_leading (radius : Coordinate) (degree : Nat)
    (positive : 0 < degree) :
    LeadingTerm (tracePolynomial radius degree) degree (2 ^ degree) := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  change LeadingTerm (tracePair radius predecessor).2
    (predecessor + 1) (2 ^ (predecessor + 1))
  exact tracePair_leading radius predecessor

/-- Subtracting the displayed target does not change the positive leading
term. -/
def coordinatePolynomial (radius target : Coordinate) (degree : Nat) :
    Polynomial :=
  tracePolynomial radius degree - normalizedConstant (2 * target)

theorem coordinatePolynomial_leading (radius target : Coordinate)
    (degree : Nat) (positive : 0 < degree) :
    LeadingTerm (coordinatePolynomial radius target degree) degree
      (2 ^ degree) := by
  have targetBelow :
      DegreeBelow (normalizedConstant (2 * target)) degree := by
    have targetAtMost := normalizedConstant_atMost (2 * target)
    exact targetAtMost.toBelowSucc.mono positive
  exact (tracePolynomial_leading radius degree positive).subBelow targetBelow

theorem coordinatePolynomial_nonzero (radius target : Coordinate)
    (degree : Nat) (positive : 0 < degree) :
    (coordinatePolynomial radius target degree).isZero = false :=
  (coordinatePolynomial_leading radius target degree positive).nonzero

theorem coordinatePolynomial_coefficients_length
    (radius target : Coordinate) (degree : Nat) (positive : 0 < degree) :
    (coordinatePolynomial radius target degree).coeffs.length = degree + 1 := by
  have leading := coordinatePolynomial_leading radius target degree positive
  have count := leading.count_eq
  change (coordinatePolynomial radius target degree).normalize.coeffs.length =
    degree + 1 at count
  rw [leading.normalized] at count
  exact count

/-! ## The sparse norm equation -/

/-- The high-to-low coefficient list of `T^q-value`, for positive `q`. -/
def powerPolynomial (value : Coordinate) (degree : Nat) : Polynomial :=
  ⟨1 :: (List.replicate (degree - 1) 0 ++ [-value])⟩

theorem powerPolynomial_normalized (value : Coordinate) (degree : Nat) :
    (powerPolynomial value degree).normalize = powerPolynomial value degree := by
  have oneNonzero : (1 : Coordinate) ≠ 0 := by decide
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  change
    (1 :: (List.replicate (degree - 1) 0 ++ [-value])).dropWhile
        (· = 0) =
      1 :: (List.replicate (degree - 1) 0 ++ [-value])
  rw [List.dropWhile_cons_of_neg (by simp [oneNonzero])]

theorem powerPolynomial_degree (value : Coordinate) (degree : Nat)
    (positive : 0 < degree) :
    (powerPolynomial value degree).natDegree = degree := by
  change (powerPolynomial value degree).normalize.coeffs.length - 1 = degree
  rw [powerPolynomial_normalized]
  simp only [powerPolynomial, List.length_cons, List.length_append,
    List.length_replicate, List.length_nil]
  rw [Nat.sub_add_cancel positive]
  exact Nat.add_sub_cancel degree 1

theorem powerPolynomial_coefficients_length (value : Coordinate)
    (degree : Nat) (positive : 0 < degree) :
    (powerPolynomial value degree).coeffs.length = degree + 1 := by
  simp only [powerPolynomial, List.length_cons, List.length_append,
    List.length_replicate, List.length_nil]
  rw [Nat.sub_add_cancel positive]

private theorem evalCoeffs_append_singleton
    (point : Coordinate) (coefficients : List Coordinate)
    (trailing : Coordinate) :
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        (coefficients ++ [trailing]) =
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point coefficients *
        point + trailing := by
  simp only [RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
    QuotientFreeList.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem powerPolynomial_eval (value point : Coordinate) (degree : Nat)
    (positive : 0 < degree) :
    (powerPolynomial value degree).eval point = point ^ degree - value := by
  have predecessor : degree - 1 + 1 = degree :=
    Nat.sub_add_cancel positive
  change RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
      (1 :: (List.replicate (degree - 1) 0 ++ [-value])) =
    point ^ degree - value
  rw [show
      1 :: (List.replicate (degree - 1) 0 ++ [-value]) =
        ([1] ++ List.replicate (degree - 1) 0) ++ [-value] by
      simp only [List.cons_append, List.nil_append]]
  rw [evalCoeffs_append_singleton,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_append_replicate_zero]
  change ((0 * point + 1) * point ^ (degree - 1)) * point + -value =
    point ^ degree - value
  calc
    (0 * point + 1) * point ^ (degree - 1) * point + -value =
        point ^ (degree - 1) * point - value := by ring1
    _ = point ^ degree - value := by
      rw [← pow_succ, predecessor]

theorem powerPolynomial_nonzero (value : Coordinate) (degree : Nat)
    (_positive : 0 < degree) :
    (powerPolynomial value degree).isZero = false := by
  have normalized := powerPolynomial_normalized value degree
  change (powerPolynomial value degree).normalize.coeffs.isEmpty = false
  rw [normalized]
  rfl

/-! ## Finite trace identity -/

/-- The Gaussian pair `(z^n+conj(z)^n,z^(n+1)+conj(z)^(n+1))`. -/
def gaussianTracePair (point : Gaussian) : Nat → Gaussian × Gaussian
  | 0 => (2, point + conj point)
  | degree + 1 =>
      let previous := gaussianTracePair point degree
      (previous.2,
        (point + conj point) * previous.2 -
          (point * conj point) * previous.1)

theorem add_conj (point : Gaussian) :
    point + conj point =
      ⟨2 * point.re, 0⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im, conj] <;> ring1

theorem mul_conj (point : Gaussian) :
    point * conj point =
      ⟨normSq point, 0⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [mul_re, mul_im, conj, normSq] <;> ring1

private theorem traceStepRing {R : Type} [CommRing R]
    (point conjugate previous next : R) :
    (point + conjugate) * (next * point + previous * conjugate) -
        point * conjugate * (next + previous) =
      next * point * point + previous * conjugate * conjugate := by
  ring1

theorem gaussianTracePair_eq_powers (point : Gaussian) : ∀ degree,
    gaussianTracePair point degree =
      (point ^ degree + conj point ^ degree,
        point ^ (degree + 1) + conj point ^ (degree + 1)) := by
  intro degree
  induction degree with
  | zero =>
      simp only [gaussianTracePair, pow_zero]
      apply Prod.ext
      · change (2 : Gaussian) = 1 + 1
        ring1
      · change point + conj point = point ^ 1 + conj point ^ 1
        rw [pow_one, pow_one]
  | succ degree inductionHypothesis =>
      rw [gaussianTracePair, inductionHypothesis]
      apply Prod.ext
      · rfl
      · change
          (point + conj point) *
                (point ^ (degree + 1) + conj point ^ (degree + 1)) -
              point * conj point *
                (point ^ degree + conj point ^ degree) =
            point ^ (Nat.succ degree + 1) +
              conj point ^ (Nat.succ degree + 1)
        have pointPower :
            point ^ (Nat.succ degree + 1) =
              point ^ degree * point * point := by
            rw [show Nat.succ degree + 1 = (degree + 1) + 1 by rfl,
              pow_succ, pow_succ]
        have conjugatePower :
            conj point ^ (Nat.succ degree + 1) =
              conj point ^ degree * conj point * conj point := by
            rw [show Nat.succ degree + 1 = (degree + 1) + 1 by rfl,
              pow_succ, pow_succ]
        rw [pointPower, conjugatePower,
          pow_succ point degree, pow_succ (conj point) degree]
        exact traceStepRing point (conj point)
          (conj point ^ degree) (point ^ degree)

theorem tracePair_eval_eq_gaussian (point : Gaussian) : ∀ degree,
    (tracePair (normSq point) degree).1.eval point.re =
        (gaussianTracePair point degree).1.re ∧
      (tracePair (normSq point) degree).2.eval point.re =
        (gaussianTracePair point degree).2.re := by
  intro degree
  induction degree with
  | zero =>
      constructor
      · change (normalizedConstant 2).eval point.re = (2 : Gaussian).re
        rw [eval_normalizedConstant]
        exact (natCast_re 2).symm
      · change twiceVariable.eval point.re = (point + conj point).re
        rw [eval_twiceVariable, add_re]
        change 2 * point.re = point.re + point.re
        ring1
  | succ degree inductionHypothesis =>
      rw [tracePair, gaussianTracePair]
      constructor
      · exact inductionHypothesis.2
      · simp only [eval_sub, eval_mul, eval_twiceVariable,
          eval_normalizedConstant]
        rw [add_conj, mul_conj]
        simp only [mul_re, sub_re]
        rw [inductionHypothesis.1, inductionHypothesis.2]
        ring1

theorem conj_pow (point : Gaussian) : ∀ degree,
    conj (point ^ degree) = conj point ^ degree
  | 0 => rfl
  | degree + 1 => by
      rw [pow_succ, pow_succ, conj_mul, conj_pow point degree]

theorem tracePolynomial_eval_power (point : Gaussian) (degree : Nat) :
    (tracePolynomial (normSq point) degree).eval point.re =
      2 * (point ^ degree).re := by
  have traceIdentity := (tracePair_eval_eq_gaussian point degree).1
  rw [gaussianTracePair_eq_powers] at traceIdentity
  have conjugatePowerReal :
      (conj point ^ degree).re = (point ^ degree).re := by
    have realPart := congrArg RFAP.ConstructiveGaussian.Gaussian.re
      (conj_pow point degree)
    exact realPart.symm
  simp only [add_re] at traceIdentity
  rw [conjugatePowerReal] at traceIdentity
  change (tracePair (normSq point) degree).1.eval point.re =
    2 * (point ^ degree).re
  calc
    (tracePair (normSq point) degree).1.eval point.re =
        (point ^ degree).re + (point ^ degree).re := traceIdentity
    _ = 2 * (point ^ degree).re := by ring1

/-- The fixed quarter-turn which exposes the imaginary coordinate as a real
coordinate. -/
def negativeImaginaryUnit : Gaussian := ⟨0, -1⟩

theorem negativeImaginaryUnit_mul_re (point : Gaussian) :
    (negativeImaginaryUnit * point).re = point.im := by
  change 0 * point.re - -1 * point.im = point.im
  ring1

theorem normSq_negativeImaginaryUnit_mul (point : Gaussian) :
    normSq (negativeImaginaryUnit * point) = normSq point := by
  rw [normSq_mul]
  change ((0 : Coordinate) ^ 2 + (-1) ^ 2) * normSq point = normSq point
  ring1

theorem coordinatePolynomial_real_root
    {input point : Gaussian} {degree : Nat} (_positive : 0 < degree)
    (power : point ^ degree = input) :
    (coordinatePolynomial (normSq point) input.re degree).eval point.re = 0 := by
  rw [coordinatePolynomial, eval_sub, tracePolynomial_eval_power,
    eval_normalizedConstant, power]
  ring1

theorem coordinatePolynomial_imaginary_root
    {input point : Gaussian} {degree : Nat} (positive : 0 < degree)
    (power : point ^ degree = input) :
    (coordinatePolynomial (normSq point)
      ((negativeImaginaryUnit ^ degree * input).re) degree).eval point.im = 0 := by
  let rotated := negativeImaginaryUnit * point
  have rotatedPower : rotated ^ degree = negativeImaginaryUnit ^ degree * input := by
    dsimp only [rotated]
    rw [mul_pow, power]
  have root := coordinatePolynomial_real_root positive rotatedPower
  rw [negativeImaginaryUnit_mul_re,
    normSq_negativeImaginaryUnit_mul] at root
  exact root

theorem powerPolynomial_norm_root
    {input point : Gaussian} {degree : Nat} (positive : 0 < degree)
    (power : point ^ degree = input) :
    (powerPolynomial (normSq input) degree).eval (normSq point) = 0 := by
  rw [powerPolynomial_eval _ _ _ positive, ← normSq_pow, power]
  ring1

end CCL.SparseRootCoordinates
