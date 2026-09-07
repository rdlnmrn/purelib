import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ComputablePolynomial

/-!
# Finite automatic differentiation for dense polynomials

The derivative is carried alongside the value in a single Horner fold.  This
module does not map into Mathlib's sparse polynomial representation.
-/

namespace RFAP.ComputableDerivative

open RFAP.ComputablePolynomial.DensePolynomial

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

abbrev Polynomial (K : Type*) := RFAP.ComputablePolynomial.DensePolynomial K

def derivativeStep (state : Polynomial K × Polynomial K) (coefficient : K) :
    Polynomial K × Polynomial K :=
  (shift 1 state.1 + constant coefficient, shift 1 state.2 + state.1)

def derivativeState (coefficients : List K) : Polynomial K × Polynomial K :=
  coefficients.foldl derivativeStep (0, 0)

def derivative (p : Polynomial K) : Polynomial K :=
  (derivativeState p.coeffs).2

private theorem derivativeState_dropWhile_zero (coefficients : List K) :
    derivativeState (coefficients.dropWhile (· = 0)) =
      derivativeState coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      by_cases zero : coefficient = 0
      · subst coefficient
        rw [List.dropWhile_cons_of_pos (by simp)]
        unfold derivativeState at inductionHypothesis ⊢
        simp only [List.foldl_cons, derivativeStep, shift_zero,
          normalize_constant_zero, zero_add_normalize, normalize_zero]
        exact inductionHypothesis
      · rw [List.dropWhile_cons_of_neg (by simpa using zero)]

/-- Removing representation-only leading zeros does not change the finite
automatic derivative program. -/
theorem derivative_normalize (p : Polynomial K) :
    derivative p.normalize = derivative p := by
  apply congrArg Prod.snd
  exact derivativeState_dropWhile_zero p.coeffs

private theorem derivativeFold_degreeCount_bounds :
    ∀ (coefficients : List K) (state : Polynomial K × Polynomial K)
      (processed : Nat),
      0 < processed →
      state.1.normalize = state.1 →
      state.2.normalize = state.2 →
      state.1.degreeCount ≤ processed →
      state.2.degreeCount + 1 ≤ processed →
      let output := coefficients.foldl derivativeStep state
      output.1.degreeCount ≤ processed + coefficients.length ∧
        output.2.degreeCount + 1 ≤ processed + coefficients.length
  | [], state, processed, _, _, _, valueBound, derivativeBound => by
      exact ⟨by simpa using valueBound, by simpa using derivativeBound⟩
  | coefficient :: coefficients, state, processed, processedPositive,
      valueNormalized, derivativeNormalized, valueBound, derivativeBound => by
      let next := derivativeStep state coefficient
      have nextValueNormalized : next.1.normalize = next.1 := by
        dsimp only [next, derivativeStep]
        exact normalize_add _ _
      have nextDerivativeNormalized : next.2.normalize = next.2 := by
        dsimp only [next, derivativeStep]
        exact normalize_add _ _
      have nextValueBound : next.1.degreeCount ≤ processed + 1 := by
        by_cases zero : coefficient = 0
        · subst coefficient
          dsimp only [next, derivativeStep]
          rw [add_constant_zero, normalize_shift]
          exact (degreeCount_shift_le 1 state.1).trans (by omega)
        · dsimp only [next, derivativeStep]
          apply (degreeCount_add_le_of_normalized
            (normalize_shift 1 state.1)
              (normalize_constant_of_ne zero)).trans
          apply max_le
          · exact (degreeCount_shift_le 1 state.1).trans (by omega)
          · exact (degreeCount_constant_le_one coefficient).trans (by omega)
      have nextDerivativeBound : next.2.degreeCount + 1 ≤ processed + 1 := by
        have raw : next.2.degreeCount ≤ processed := by
          dsimp only [next, derivativeStep]
          apply (degreeCount_add_le_of_normalized
            (normalize_shift 1 state.2) valueNormalized).trans
          apply max_le
          · exact (degreeCount_shift_le 1 state.2).trans (by omega)
          · exact valueBound
        omega
      simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        derivativeFold_degreeCount_bounds coefficients next
          (processed + 1) (by omega) nextValueNormalized
            nextDerivativeNormalized nextValueBound nextDerivativeBound

/-- The automatic derivative has at most one fewer normalized coefficient
slot than a represented nonzero polynomial. -/
theorem derivative_degreeCount_add_one_le
    {p : Polynomial K} (nonzero : p.isZero = false) :
    (derivative p).degreeCount + 1 ≤ p.degreeCount := by
  rw [← derivative_normalize p]
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.isEmpty = false at nonzero
      rw [coefficients] at nonzero
      exact Bool.noConfusion nonzero
  | cons leading tail =>
      let initial := derivativeStep (0, 0) leading
      have initialValueNormalized : initial.1.normalize = initial.1 := by
        dsimp only [initial, derivativeStep]
        exact normalize_add _ _
      have initialDerivativeNormalized : initial.2.normalize = initial.2 := by
        dsimp only [initial, derivativeStep]
        exact normalize_add _ _
      have initialValueBound : initial.1.degreeCount ≤ 1 := by
        dsimp only [initial, derivativeStep]
        apply (degreeCount_add_le_of_normalized
          (normalize_shift 1 (0 : Polynomial K)) (normalize_constant_of_ne
            (show leading ≠ 0 from by
              have canonical := leadingCoeff_ne_zero nonzero
              change p.normalize.coeffs.headD 0 ≠ 0 at canonical
              rw [coefficients] at canonical
              simpa only [List.headD_cons] using canonical))).trans
        apply max_le
        · change (normalize (0 : Polynomial K)).coeffs.length ≤ 1
          rw [normalize_zero]
          exact Nat.zero_le _
        · exact degreeCount_constant_le_one leading
      have initialDerivativeBound : initial.2.degreeCount + 1 ≤ 1 := by
        have initialDerivativeZero : initial.2 = (0 : Polynomial K) := by
          dsimp only [initial, derivativeStep]
          rw [shift_zero, add_zero_normalize, normalize_zero]
        rw [initialDerivativeZero, degreeCount]
        exact le_rfl
      have bounds := derivativeFold_degreeCount_bounds tail initial 1
        (by decide) initialValueNormalized initialDerivativeNormalized
          initialValueBound initialDerivativeBound
      change ((derivativeState p.normalize.coeffs).2).degreeCount + 1 ≤
        p.normalize.coeffs.length
      rw [coefficients]
      simpa only [derivativeState, List.foldl_cons, List.length_cons,
        Nat.add_comm]
        using bounds.2

/-- Strict characteristic-zero derivative degree descent, proved from the
finite coefficient scan rather than an imported polynomial theorem. -/
theorem derivative_natDegree_lt
    {p : Polynomial K} (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) :
    (derivative p).natDegree < p.natDegree := by
  have countBound := derivative_degreeCount_add_one_le nonzero
  by_cases derivativeZero : (derivative p).isZero = true
  · have derivativeDegreeZero : (derivative p).natDegree = 0 := by
      rw [natDegree, degreeCount_eq_zero_of_isZero derivativeZero]
    rw [derivativeDegreeZero]
    exact positive
  · have derivativeNonzero : (derivative p).isZero = false := by
      simpa using derivativeZero
    have derivativeCount :=
      natDegree_add_one_eq_degreeCount derivativeNonzero
    have originalCount := natDegree_add_one_eq_degreeCount nonzero
    omega

def evalDerivativeStep (x : K) (state : K × K) (coefficient : K) : K × K :=
  (state.1 * x + coefficient, state.2 * x + state.1)

def evalDerivativeCoeffs (x : K) (coefficients : List K) : K × K :=
  coefficients.foldl (evalDerivativeStep x) (0, 0)

private theorem eval_derivativeFold
    (x : K) (coefficients : List K) (state : Polynomial K × Polynomial K) :
    ((coefficients.foldl derivativeStep state).1.eval x,
        (coefficients.foldl derivativeStep state).2.eval x) =
      coefficients.foldl (evalDerivativeStep x)
        (state.1.eval x, state.2.eval x) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      rw [ih]
      apply Prod.ext
      · simp only [derivativeStep, evalDerivativeStep, eval_add, eval_shift,
          eval_constant, pow_one]
      · simp only [derivativeStep, evalDerivativeStep, eval_add, eval_shift,
          eval_constant, pow_one]

omit [DecidableEq K] in
private theorem evalDerivativeCoeffs_fst
    (x : K) (coefficients : List K) (value derivativeValue : K) :
    (coefficients.foldl (evalDerivativeStep x) (value, derivativeValue)).1 =
      coefficients.foldl (fun acc coefficient => acc * x + coefficient) value := by
  induction coefficients generalizing value derivativeValue with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons, evalDerivativeStep]
      exact ih (value * x + coefficient) (derivativeValue * x + value)

theorem eval_derivative (p : Polynomial K) (x : K) :
    (derivative p).eval x = (evalDerivativeCoeffs x p.coeffs).2 := by
  have specification := eval_derivativeFold x p.coeffs (0, 0)
  exact congrArg Prod.snd specification

omit [DecidableEq K] in
theorem eval_original (p : Polynomial K) (x : K) :
    (evalDerivativeCoeffs x p.coeffs).1 = p.eval x := by
  exact evalDerivativeCoeffs_fst x p.coeffs 0 0

/-- Removing representation-only leading zeros preserves both Horner value
and automatic derivative value. -/
theorem evalDerivativeCoeffs_normalize (p : Polynomial K) (x : K) :
    evalDerivativeCoeffs x p.normalize.coeffs =
      evalDerivativeCoeffs x p.coeffs := by
  apply Prod.ext
  · rw [eval_original, eval_original, eval_normalize]
  · rw [← eval_derivative, ← eval_derivative,
      derivative_normalize]

omit [DecidableEq K] in
private theorem foldl_evalDerivative_map_scale
    (c x : K) : ∀ (coefficients : List K) (value derivativeValue : K),
    (coefficients.map (c * ·)).foldl (evalDerivativeStep x)
        (c * value, c * derivativeValue) =
      let result := coefficients.foldl (evalDerivativeStep x)
        (value, derivativeValue)
      (c * result.1, c * result.2)
  | [], _, _ => rfl
  | coefficient :: coefficients, value, derivativeValue => by
      simp only [List.map_cons, List.foldl_cons, evalDerivativeStep]
      have valueStep :
          c * value * x + c * coefficient =
            c * (value * x + coefficient) := by ring1
      have derivativeStep :
          c * derivativeValue * x + c * value =
            c * (derivativeValue * x + value) := by ring1
      rw [valueStep, derivativeStep]
      exact foldl_evalDerivative_map_scale c x coefficients
        (value * x + coefficient) (derivativeValue * x + value)

/-- Scalar multiplication commutes pointwise with the finite automatic
derivative. -/
theorem eval_derivative_scale (c : K) (p : Polynomial K) (x : K) :
    (derivative (scale c p)).eval x = c * (derivative p).eval x := by
  by_cases zero : c = 0
  · subst c
    rw [scale_zero_left, zero_mul, eval_derivative]
    rfl
  · rw [eval_derivative, scale_coeffs_of_ne_zero zero]
    have scaled := foldl_evalDerivative_map_scale c x p.normalize.coeffs 0 0
    simp only [mul_zero] at scaled
    change ((p.normalize.coeffs.map (c * ·)).foldl
      (evalDerivativeStep x) (0, 0)).2 = _
    rw [scaled]
    change c * (evalDerivativeCoeffs x p.normalize.coeffs).2 = _
    rw [evalDerivativeCoeffs_normalize]
    rw [← eval_derivative]

/-- Appending one zero coefficient is multiplication by the variable, whose
derivative obeys the direct Horner rule. -/
theorem eval_derivative_shift_one (p : Polynomial K) (x : K) :
    (derivative (shift 1 p)).eval x =
      (derivative p).eval x * x + p.eval x := by
  by_cases zero : p.isZero = true
  · rw [shift, if_pos zero, eval_derivative]
    have pEvalZero := eval_eq_zero_of_isZero zero x
    rw [pEvalZero]
    have derivativeZero : derivative p = 0 := by
      rw [← derivative_normalize p, normalize_eq_zero_of_isZero zero]
      rfl
    rw [derivativeZero, eval_zero, zero_mul, zero_add]
    rfl
  · have nonzero : p.isZero = false := by simpa using zero
    have coefficients : (shift 1 p).coeffs = p.normalize.coeffs ++ [0] := by
      rw [shift, if_neg (by simpa using nonzero)]
      simp only [List.replicate_succ, List.replicate_zero]
    rw [eval_derivative, coefficients]
    simp only [evalDerivativeCoeffs, QuotientFreeList.foldl_append, List.foldl_cons,
      List.foldl_nil, evalDerivativeStep]
    rw [← evalDerivativeCoeffs]
    rw [evalDerivativeCoeffs_normalize]
    change (evalDerivativeCoeffs x p.coeffs).2 * x +
      (evalDerivativeCoeffs x p.coeffs).1 = _
    rw [← eval_derivative, eval_original]

omit [DecidableEq K] in
private theorem foldl_evalDerivative_replicate_zero_append
    (x : K) (count : Nat) (coefficients : List K) :
    (List.replicate count 0 ++ coefficients).foldl
        (evalDerivativeStep x) (0, 0) =
      coefficients.foldl (evalDerivativeStep x) (0, 0) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append, List.foldl_cons,
        evalDerivativeStep, zero_mul, zero_add]
      exact inductionHypothesis

omit [DecidableEq K] in
private theorem foldl_evalDerivative_zipWith_add
    (x : K) (left : List K) : ∀ (right : List K)
      (leftValue leftDerivative rightValue rightDerivative : K),
      left.length = right.length →
      (List.zipWith (· + ·) left right).foldl
          (evalDerivativeStep x)
          (leftValue + rightValue, leftDerivative + rightDerivative) =
        let leftResult := left.foldl (evalDerivativeStep x)
          (leftValue, leftDerivative)
        let rightResult := right.foldl (evalDerivativeStep x)
          (rightValue, rightDerivative)
        (leftResult.1 + rightResult.1,
          leftResult.2 + rightResult.2) := by
  induction left with
  | nil =>
      intro right leftValue leftDerivative rightValue rightDerivative length
      cases right with
      | nil => rfl
      | cons right rightTail =>
          simp only [List.length_nil, List.length_cons] at length
          exact Nat.noConfusion length
  | cons left leftTail inductionHypothesis =>
      intro right leftValue leftDerivative rightValue rightDerivative length
      cases right with
      | nil =>
          simp only [List.length_nil, List.length_cons] at length
          exact Nat.noConfusion length.symm
      | cons right rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          simp only [List.zipWith_cons_cons, List.foldl_cons,
            evalDerivativeStep]
          have valueStep :
              (leftValue + rightValue) * x + (left + right) =
                (leftValue * x + left) +
                  (rightValue * x + right) := by ring1
          have derivativeStep :
              (leftDerivative + rightDerivative) * x +
                  (leftValue + rightValue) =
                (leftDerivative * x + leftValue) +
                  (rightDerivative * x + rightValue) := by ring1
          rw [valueStep, derivativeStep]
          exact inductionHypothesis rightTail
            (leftValue * x + left) (leftDerivative * x + leftValue)
            (rightValue * x + right) (rightDerivative * x + rightValue) length

/-- Addition commutes pointwise with the finite automatic derivative. -/
theorem eval_derivative_add (p q : Polynomial K) (x : K) :
    (derivative (p + q)).eval x =
      (derivative p).eval x + (derivative q).eval x := by
  let count := max p.coeffs.length q.coeffs.length
  let left := padLeft (count - p.coeffs.length) p.coeffs
  let right := padLeft (count - q.coeffs.length) q.coeffs
  have pLength : p.coeffs.length ≤ count := le_max_left _ _
  have qLength : q.coeffs.length ≤ count := le_max_right _ _
  have leftLength : left.length = count := by
    dsimp only [left, padLeft]
    rw [List.length_append, List.length_replicate,
      Nat.sub_add_cancel pLength]
  have rightLength : right.length = count := by
    dsimp only [right, padLeft]
    rw [List.length_append, List.length_replicate,
      Nat.sub_add_cancel qLength]
  let raw : Polynomial K := ⟨List.zipWith (· + ·) left right⟩
  have sumCoefficients : (p + q).coeffs = raw.normalize.coeffs := rfl
  rw [eval_derivative, sumCoefficients]
  rw [evalDerivativeCoeffs_normalize raw]
  change ((List.zipWith (· + ·) left right).foldl
    (evalDerivativeStep x) (0, 0)).2 = _
  have combined := foldl_evalDerivative_zipWith_add x left right 0 0 0 0
    (leftLength.trans rightLength.symm)
  simp only [zero_add] at combined
  rw [combined]
  have leftPadding := foldl_evalDerivative_replicate_zero_append x
    (count - p.coeffs.length) p.coeffs
  have rightPadding := foldl_evalDerivative_replicate_zero_append x
    (count - q.coeffs.length) q.coeffs
  change (left.foldl (evalDerivativeStep x) (0, 0)).2 +
      (right.foldl (evalDerivativeStep x) (0, 0)).2 = _
  dsimp only [left, right, padLeft]
  rw [leftPadding, rightPadding]
  change (evalDerivativeCoeffs x p.coeffs).2 +
      (evalDerivativeCoeffs x q.coeffs).2 = _
  rw [← eval_derivative, ← eval_derivative]

/-- Negation commutes pointwise with the finite automatic derivative. -/
theorem eval_derivative_neg (p : Polynomial K) (x : K) :
    (derivative (-p)).eval x = -(derivative p).eval x := by
  have scaleNegOne : scale (-1) p = -p := by
    rw [scale_neg_left, scale_one_left, neg_normalize]
  rw [← scaleNegOne, eval_derivative_scale, neg_one_mul]

/-- Subtraction commutes pointwise with the finite automatic derivative. -/
theorem eval_derivative_sub (p q : Polynomial K) (x : K) :
    (derivative (p - q)).eval x =
      (derivative p).eval x - (derivative q).eval x := by
  change (derivative (p + -q)).eval x = _
  rw [eval_derivative_add, eval_derivative_neg]
  exact (sub_eq_add_neg _ _).symm

/-- A finite zero coefficient difference also has equal automatic derivative
values; no evaluation-extensionality or infinite carrier is involved. -/
theorem eval_derivative_eq_of_sub_isZero
    {p q : Polynomial K} (same : (p - q).isZero = true) (x : K) :
    (derivative p).eval x = (derivative q).eval x := by
  have differenceDerivativeZero : derivative (p - q) = 0 := by
    rw [← derivative_normalize (p - q),
      normalize_eq_zero_of_isZero same]
    rfl
  have differenceEvalZero : (derivative (p - q)).eval x = 0 := by
    rw [differenceDerivativeZero, eval_zero]
  rw [eval_derivative_sub] at differenceEvalZero
  exact sub_eq_zero.mp differenceEvalZero

private theorem eval_derivative_mulFold
    (q : Polynomial K) (x : K) :
    ∀ (coefficients : List K) (accumulator : Polynomial K)
      (value derivativeValue : K),
      accumulator.eval x = value * q.eval x →
      (derivative accumulator).eval x =
        derivativeValue * q.eval x + value * (derivative q).eval x →
      let scalarResult := coefficients.foldl (evalDerivativeStep x)
        (value, derivativeValue)
      let polynomialResult := coefficients.foldl
        (fun result coefficient => shift 1 result + scale coefficient q)
        accumulator
      polynomialResult.eval x = scalarResult.1 * q.eval x ∧
        (derivative polynomialResult).eval x =
          scalarResult.2 * q.eval x +
            scalarResult.1 * (derivative q).eval x
  | [], accumulator, value, derivativeValue, valueSpec, derivativeSpec =>
      ⟨valueSpec, derivativeSpec⟩
  | coefficient :: coefficients, accumulator, value, derivativeValue,
      valueSpec, derivativeSpec => by
      let next := shift 1 accumulator + scale coefficient q
      have nextValue : next.eval x =
          (value * x + coefficient) * q.eval x := by
        dsimp only [next]
        rw [eval_add, eval_shift, eval_scale, pow_one, valueSpec]
        ring1
      have nextDerivative : (derivative next).eval x =
          (derivativeValue * x + value) * q.eval x +
            (value * x + coefficient) * (derivative q).eval x := by
        dsimp only [next]
        rw [eval_derivative_add, eval_derivative_shift_one,
          eval_derivative_scale, derivativeSpec, valueSpec]
        ring1
      simpa only [List.foldl_cons, evalDerivativeStep] using
        eval_derivative_mulFold q x coefficients next
          (value * x + coefficient) (derivativeValue * x + value)
            nextValue nextDerivative

/-- Direct finite product rule for the executable Horner derivative. -/
theorem eval_derivative_mul (p q : Polynomial K) (x : K) :
    (derivative (p * q)).eval x =
      (derivative p).eval x * q.eval x +
        p.eval x * (derivative q).eval x := by
  have result := eval_derivative_mulFold q x p.coeffs 0 0 0
    (by simp only [eval_zero, zero_mul])
    (by
      simp only [zero_mul, zero_add]
      rw [eval_derivative]
      rfl)
  change (derivative (p.coeffs.foldl
    (fun accumulator coefficient =>
      shift 1 accumulator + scale coefficient q) 0)).eval x = _
  have derivativeResult := result.2
  change (derivative (p.coeffs.foldl
      (fun accumulator coefficient =>
        shift 1 accumulator + scale coefficient q) 0)).eval x =
    (evalDerivativeCoeffs x p.coeffs).2 * q.eval x +
      (evalDerivativeCoeffs x p.coeffs).1 *
        (derivative q).eval x at derivativeResult
  rw [← eval_derivative, eval_original] at derivativeResult
  exact derivativeResult

end RFAP.ComputableDerivative
