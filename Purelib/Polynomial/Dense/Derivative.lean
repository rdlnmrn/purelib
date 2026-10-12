module
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Fold
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication

import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Finite automatic differentiation for dense polynomials

The derivative is carried alongside the value in a single Horner fold.  This
module does not map into Mathlib's sparse polynomial representation.
-/

namespace Purelib.Polynomial.Dense.Derivative

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Data.List
open Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The retained descending dense polynomial representation over the supplied coefficient field. -/
abbrev CoefficientPolynomial (K : Type*) := DensePolynomial K

/-- Advance the polynomial value-and-derivative state by one descending coefficient.

Shift the value and add the new constant; shift the derivative and add the preceding value polynomial. -/
@[expose] def derivativeStep (state : CoefficientPolynomial K × CoefficientPolynomial K) (coefficient : K) :
    CoefficientPolynomial K × CoefficientPolynomial K :=
  (DensePolynomial.shift 1 state.1 + DensePolynomial.constant coefficient, DensePolynomial.shift 1 state.2 + state.1)

/-- Compute the polynomial and derivative together in a finite Horner fold starting from two zeros.

The original finite coefficient fold starts at two zero polynomial owners.
Each displayed descending coefficient updates the same value-and-derivative pair. -/
@[expose] def derivativeState (coefficients : List K) : CoefficientPolynomial K × CoefficientPolynomial K :=
  coefficients.foldl derivativeStep (0, 0)

/-- Return the derivative component of the finite polynomial Horner state.

The retained input coefficient spine feeds the original polynomial-state fold.
The resulting second component supplies its same normalized derivative representation. -/
@[expose] def derivative (p : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (derivativeState p.coeffs).2

/-- Dropping leading zero coefficients preserves both polynomials in the derivative state.

A zero coefficient leaves the original zero starting pair unchanged.
The original Boolean test removes only those displayed leading zeros. -/
private theorem derivativeState_dropWhile_zero (coefficients : List K) :
    derivativeState (coefficients.dropWhile (· = 0)) =
      derivativeState coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      by_cases zero : coefficient = 0
      · subst coefficient
        rewrite [DropWhile.cons_of_true (fun value : K => decide (value = 0))
          0 coefficients (decide_eq_true (Eq.refl (0 : K)))]
        unfold derivativeState at inductionHypothesis ⊢
        simp only [List.foldl_cons, derivativeStep, DensePolynomial.shift_zero,
          DensePolynomial.normalize_constant_zero, DensePolynomial.zero_add_normalize, DensePolynomial.normalize_zero]
        exact inductionHypothesis
      · rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
          coefficient coefficients (decide_eq_false zero)]

/-- Removing representation-only leading zeros does not change the finite
automatic derivative program.

The original normalization removes the finite zero prefix before the same
polynomial-state fold, whose two original accumulators are preserved. -/
theorem derivative_normalize (p : CoefficientPolynomial K) :
    derivative p.normalize = derivative p := by
  apply congrArg Prod.snd
  exact derivativeState_dropWhile_zero p.coeffs

/-- Track value and derivative degree counts through a finite coefficient fold.

The normalized initial value has at most `processed` slots and the derivative at most one fewer; scanning the remaining
list extends both bounds by its length. -/
private theorem derivativeFold_degreeCount_bounds :
    ∀ (coefficients : List K) (state : CoefficientPolynomial K × CoefficientPolynomial K)
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
        exact DensePolynomial.normalize_add _ _
      have nextDerivativeNormalized : next.2.normalize = next.2 := by
        dsimp only [next, derivativeStep]
        exact DensePolynomial.normalize_add _ _
      have nextValueBound : next.1.degreeCount ≤ processed + 1 := by
        by_cases zero : coefficient = 0
        · subst coefficient
          dsimp only [next, derivativeStep]
          rw [DensePolynomial.add_constant_zero, DensePolynomial.normalize_shift]
          exact (DensePolynomial.degreeCount_shift_le 1 state.1).trans (by omega)
        · dsimp only [next, derivativeStep]
          apply (DensePolynomial.degreeCount_add_le_of_normalized
            (DensePolynomial.normalize_shift 1 state.1)
              (DensePolynomial.normalize_constant_of_ne zero)).trans
          apply Order.max_le
          · exact (DensePolynomial.degreeCount_shift_le 1 state.1).trans (by omega)
          · exact (DensePolynomial.degreeCount_constant_le_one coefficient).trans (by omega)
      have nextDerivativeBound : next.2.degreeCount + 1 ≤ processed + 1 := by
        have raw : next.2.degreeCount ≤ processed := by
          dsimp only [next, derivativeStep]
          apply (DensePolynomial.degreeCount_add_le_of_normalized
            (DensePolynomial.normalize_shift 1 state.2) valueNormalized).trans
          apply Order.max_le
          · exact (DensePolynomial.degreeCount_shift_le 1 state.2).trans (by omega)
          · exact valueBound
        omega
      simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        derivativeFold_degreeCount_bounds coefficients next
          (processed + 1) (by omega) nextValueNormalized
            nextDerivativeNormalized nextValueBound nextDerivativeBound

/-- The automatic derivative has at most one fewer normalized coefficient
slot than a represented nonzero polynomial.

The original nonzero normalized input has a retained first coefficient.
The same finite scan keeps at most one fewer derivative slot throughout the fold. -/
theorem derivative_degreeCount_add_one_le
    {p : CoefficientPolynomial K} (nonzero : p.isZero = false) :
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
        exact DensePolynomial.normalize_add _ _
      have initialDerivativeNormalized : initial.2.normalize = initial.2 := by
        dsimp only [initial, derivativeStep]
        exact DensePolynomial.normalize_add _ _
      have initialValueBound : initial.1.degreeCount ≤ 1 := by
        dsimp only [initial, derivativeStep]
        apply (DensePolynomial.degreeCount_add_le_of_normalized
          (DensePolynomial.normalize_shift 1 (0 : CoefficientPolynomial K)) (DensePolynomial.normalize_constant_of_ne
            (show leading ≠ 0 from by
              have canonical := DensePolynomial.leadingCoeff_ne_zero nonzero
              change p.normalize.coeffs.headD 0 ≠ 0 at canonical
              rw [coefficients] at canonical
              simpa only [List.headD_cons] using canonical))).trans
        apply Order.max_le
        · change (DensePolynomial.normalize (0 : CoefficientPolynomial K)).coeffs.length ≤ 1
          rw [DensePolynomial.normalize_zero]
          exact Nat.zero_le _
        · exact DensePolynomial.degreeCount_constant_le_one leading
      have initialDerivativeBound : initial.2.degreeCount + 1 ≤ 1 := by
        have initialDerivativeZero : initial.2 = (0 : CoefficientPolynomial K) := by
          dsimp only [initial, derivativeStep]
          rw [DensePolynomial.shift_zero, DensePolynomial.add_zero_normalize, DensePolynomial.normalize_zero]
        rw [initialDerivativeZero, DensePolynomial.degreeCount]
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

/-- The automatic derivative has smaller natural degree than a represented nonzero positive-degree polynomial.

The finite coefficient-count bound handles both a zero derivative and a nonzero derivative; no characteristic assumption
is needed. -/
theorem derivative_natDegree_lt
    {p : CoefficientPolynomial K} (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) :
    (derivative p).natDegree < p.natDegree := by
  have countBound := derivative_degreeCount_add_one_le nonzero
  by_cases derivativeZero : (derivative p).isZero = true
  · have derivativeDegreeZero : (derivative p).natDegree = 0 := by
      rewrite [DensePolynomial.natDegree,
        DensePolynomial.degreeCount_eq_zero_of_isZero derivativeZero]
      exact Eq.refl _
    rw [derivativeDegreeZero]
    exact positive
  · have derivativeNonzero : (derivative p).isZero = false := by
      cases observed : (derivative p).isZero with
      | false => rfl
      | true => exact (derivativeZero observed).elim
    have derivativeCount :=
      DensePolynomial.natDegree_add_one_eq_degreeCount derivativeNonzero
    have originalCount := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
    omega

/-- Advance a scalar value-and-derivative Horner state at the supplied point.

The original value is shifted before its coefficient is added. The derivative
uses that retained preceding value and the same supplied evaluation point. -/
@[expose] def evalDerivativeStep (x : K) (state : K × K) (coefficient : K) : K × K :=
  (state.1 * x + coefficient, state.2 * x + state.1)

/-- Compute the value and derivative value together from descending coefficients.

The original descending table feeds the same scalar pair recurrence.
Both components start at zero and retain the supplied point at every entry. -/
@[expose] def evalDerivativeCoeffs (x : K) (coefficients : List K) : K × K :=
  coefficients.foldl (evalDerivativeStep x) (0, 0)

/-- Evaluating the polynomial derivative-state fold agrees with the scalar state fold.

The initial scalar state is the pair of evaluations of the retained polynomial accumulators. -/
private theorem eval_derivativeFold
    (x : K) (coefficients : List K) (state : CoefficientPolynomial K × CoefficientPolynomial K) :
    ((coefficients.foldl derivativeStep state).1.eval x,
        (coefficients.foldl derivativeStep state).2.eval x) =
      coefficients.foldl (evalDerivativeStep x)
        (state.1.eval x, state.2.eval x) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have stepEquality :
          ((derivativeStep state coefficient).1.eval x,
            (derivativeStep state coefficient).2.eval x) =
          evalDerivativeStep x
            (state.1.eval x, state.2.eval x) coefficient := by
        apply Prod.ext
        · change (DensePolynomial.shift 1 state.1 +
              DensePolynomial.constant coefficient).eval x =
            state.1.eval x * x + coefficient
          rewrite [DensePolynomial.eval_add,
            DensePolynomial.eval_shift,
            DensePolynomial.eval_constant, pow_one]
          exact Eq.refl _
        · change (DensePolynomial.shift 1 state.2 + state.1).eval x =
            state.2.eval x * x + state.1.eval x
          rewrite [DensePolynomial.eval_add,
            DensePolynomial.eval_shift, pow_one]
          exact Eq.refl _
      exact congrArg (fun initial => coefficients.foldl
        (evalDerivativeStep x) initial) stepEquality

omit [DecidableEq K] in
/-- The first component of a derivative-state fold is ordinary Horner evaluation from its initial value.

Each displayed original coefficient performs the same value update in both
folds. The derivative accumulator does not alter those retained value steps. -/
private theorem evalDerivativeCoeffs_fst
    (x : K) (coefficients : List K) (value derivativeValue : K) :
    (coefficients.foldl (evalDerivativeStep x) (value, derivativeValue)).1 =
      coefficients.foldl (fun acc coefficient => acc * x + coefficient) value := by
  induction coefficients generalizing value derivativeValue with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons, evalDerivativeStep]
      exact ih (value * x + coefficient) (derivativeValue * x + value)

/-- The executable derivative evaluates to the second component of the scalar Horner state.

The same original coefficient table feeds the polynomial and scalar folds.
Evaluation of the retained derivative component agrees with the second scalar value. -/
theorem eval_derivative (p : CoefficientPolynomial K) (x : K) :
    (derivative p).eval x = (evalDerivativeCoeffs x p.coeffs).2 := by
  have specification := eval_derivativeFold x p.coeffs (0, 0)
  exact congrArg Prod.snd specification

omit [DecidableEq K] in
/-- The first scalar Horner-state component is the original polynomial value.

The first scalar component has exactly the retained descending Horner value.
The derivative component does not change that original input table or scalar scan. -/
theorem eval_original (p : CoefficientPolynomial K) (x : K) :
    (evalDerivativeCoeffs x p.coeffs).1 = p.eval x := by
  exact evalDerivativeCoeffs_fst x p.coeffs 0 0

/-- Removing representation-only leading zeros preserves both Horner value
and automatic derivative value.

Each original leading zero preserves both zero starting accumulators.
The normalized coefficient table therefore yields the same scalar pair. -/
theorem evalDerivativeCoeffs_normalize (p : CoefficientPolynomial K) (x : K) :
    evalDerivativeCoeffs x p.normalize.coeffs =
      evalDerivativeCoeffs x p.coeffs := by
  apply Prod.ext
  · rw [eval_original, eval_original, DensePolynomial.eval_normalize]
  · rw [← eval_derivative, ← eval_derivative,
      derivative_normalize]

omit [DecidableEq K] in
/-- Scaling coefficients and both initial state components scales both final Horner-state components.

Each retained coefficient and both original scalar accumulators receive
the same factor. The unchanged finite scan distributes that factor pointwise. -/
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
derivative.

The original coefficient scaling and normalization preserve the scalar pair
fold, so its derivative readback receives the same supplied scalar factor. -/
theorem eval_derivative_scale (c : K) (p : CoefficientPolynomial K) (x : K) :
    (derivative (DensePolynomial.scale c p)).eval x = c * (derivative p).eval x := by
  by_cases zero : c = 0
  · subst c
    rw [DensePolynomial.scale_zero_left, zero_mul, eval_derivative]
    rfl
  · rw [eval_derivative, DensePolynomial.scale_coeffs_of_ne_zero zero]
    have scaled := foldl_evalDerivative_map_scale c x p.normalize.coeffs 0 0
    simp only [mul_zero] at scaled
    change ((p.normalize.coeffs.map (c * ·)).foldl
      (evalDerivativeStep x) (0, 0)).2 = _
    rw [scaled]
    change c * (evalDerivativeCoeffs x p.normalize.coeffs).2 = _
    rw [evalDerivativeCoeffs_normalize]
    rw [← eval_derivative]

/-- Appending one zero coefficient is multiplication by the variable, whose
derivative obeys the direct Horner rule.

The original appended zero shifts the retained polynomial once. Its scalar
Horner update preserves the preceding value contribution to the derivative. -/
theorem eval_derivative_shift_one (p : CoefficientPolynomial K) (x : K) :
    (derivative (DensePolynomial.shift 1 p)).eval x =
      (derivative p).eval x * x + p.eval x := by
  by_cases zero : p.isZero = true
  · rw [DensePolynomial.shift, if_pos zero, eval_derivative]
    have pEvalZero := DensePolynomial.eval_eq_zero_of_isZero zero x
    rw [pEvalZero]
    have derivativeZero : derivative p = 0 := by
      rw [← derivative_normalize p, DensePolynomial.normalize_eq_zero_of_isZero zero]
      rfl
    rw [derivativeZero, DensePolynomial.eval_zero, zero_mul, zero_add]
    rfl
  · have coefficients : (DensePolynomial.shift 1 p).coeffs = p.normalize.coeffs ++ [0] := by
      rewrite [DensePolynomial.shift, if_neg zero]
      exact Eq.refl _
    rw [eval_derivative, coefficients]
    simp only [evalDerivativeCoeffs, Fold.foldl_append, List.foldl_cons,
      List.foldl_nil, evalDerivativeStep]
    rw [← evalDerivativeCoeffs]
    rw [evalDerivativeCoeffs_normalize]
    change (evalDerivativeCoeffs x p.coeffs).2 * x +
      (evalDerivativeCoeffs x p.coeffs).1 = _
    rewrite [← eval_derivative, eval_original]
    exact Eq.refl _

omit [DecidableEq K] in
/-- A prefixed zero block does not change the value-and-derivative fold starting at zero.

Every original padding zero leaves the zero scalar pair unchanged.
The retained table begins after the same finite padding prefix. -/
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
/-- Equal-length coefficient-list addition preserves addition of value-and-derivative Horner states.

The supplied length equality identifies the paired original slots.
Each pair adds its scalar updates before recursion on the unchanged two tails. -/
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
          cases length
  | cons left leftTail inductionHypothesis =>
      intro right leftValue leftDerivative rightValue rightDerivative length
      cases right with
      | nil =>
          cases length
      | cons right rightTail =>
          have tailLength : leftTail.length = rightTail.length := Nat.succ.inj length
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
            (rightValue * x + right) (rightDerivative * x + rightValue) tailLength

/-- Addition commutes pointwise with the finite automatic derivative.

The original maximum-length padding and zip preserve both input tables.
The scalar pair fold adds their same derivative readbacks pointwise. -/
theorem eval_derivative_add (p q : CoefficientPolynomial K) (x : K) :
    (derivative (p + q)).eval x =
      (derivative p).eval x + (derivative q).eval x := by
  let count := max p.coeffs.length q.coeffs.length
  let left := DensePolynomial.padLeft (count - p.coeffs.length) p.coeffs
  let right := DensePolynomial.padLeft (count - q.coeffs.length) q.coeffs
  have pLength : p.coeffs.length ≤ count := Order.le_max_left _ _
  have qLength : q.coeffs.length ≤ count := Order.le_max_right _ _
  have leftLength : left.length = count := by
    dsimp only [left, DensePolynomial.padLeft]
    rewrite [Append.length_append, Replicate.length_replicate,
      Nat.add_comm (count - p.coeffs.length) p.coeffs.length]
    exact Subtraction.add_sub_of_le pLength
  have rightLength : right.length = count := by
    dsimp only [right, DensePolynomial.padLeft]
    rewrite [Append.length_append, Replicate.length_replicate,
      Nat.add_comm (count - q.coeffs.length) q.coeffs.length]
    exact Subtraction.add_sub_of_le qLength
  let raw : CoefficientPolynomial K := ⟨List.zipWith (· + ·) left right⟩
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
  dsimp only [left, right, DensePolynomial.padLeft]
  rw [leftPadding, rightPadding]
  change (evalDerivativeCoeffs x p.coeffs).2 +
      (evalDerivativeCoeffs x q.coeffs).2 = _
  rw [← eval_derivative, ← eval_derivative]

/-- Negation commutes pointwise with the finite automatic derivative.

Negative-unit coefficient scaling keeps the original table order.
Its scalar derivative readback is the negation of the retained derivative value. -/
theorem eval_derivative_neg (p : CoefficientPolynomial K) (x : K) :
    (derivative (-p)).eval x = -(derivative p).eval x := by
  have scaleNegOne : DensePolynomial.scale (-1) p = -p := by
    rw [DensePolynomial.scale_neg_left, DensePolynomial.scale_one_left, DensePolynomial.neg_normalize]
  rewrite [← scaleNegOne, eval_derivative_scale]
  ring0

/-- Subtraction commutes pointwise with the finite automatic derivative.

The original subtraction adds the retained negated right polynomial.
The same scalar derivative readbacks obey that displayed difference. -/
theorem eval_derivative_sub (p q : CoefficientPolynomial K) (x : K) :
    (derivative (p - q)).eval x =
      (derivative p).eval x - (derivative q).eval x := by
  change (derivative (p + -q)).eval x = _
  rw [eval_derivative_add, eval_derivative_neg]
  exact (sub_eq_add_neg _ _).symm

/-- A finite zero coefficient difference also has equal automatic derivative
values; no evaluation-extensionality or infinite carrier is involved.

The retained coefficient difference normalizes to zero. Its original finite
derivative fold then gives zero, forcing equality of the two scalar readbacks. -/
theorem eval_derivative_eq_of_sub_isZero
    {p q : CoefficientPolynomial K} (same : (p - q).isZero = true) (x : K) :
    (derivative p).eval x = (derivative q).eval x := by
  have differenceDerivativeZero : derivative (p - q) = 0 := by
    rw [← derivative_normalize (p - q),
      DensePolynomial.normalize_eq_zero_of_isZero same]
    rfl
  have differenceEvalZero : (derivative (p - q)).eval x = 0 := by
    rw [differenceDerivativeZero, DensePolynomial.eval_zero]
  rw [eval_derivative_sub] at differenceEvalZero
  calc
    (derivative p).eval x =
        ((derivative p).eval x -
          (derivative q).eval x) +
          (derivative q).eval x := by ring0
    _ = 0 + (derivative q).eval x :=
      congrArg (fun value => value + (derivative q).eval x)
        differenceEvalZero
    _ = (derivative q).eval x := zero_add _

/-- Propagate the product rule through the finite polynomial multiplication fold.

The accumulator value equals its scalar state times the fixed right-factor value, and its derivative retains both
product-rule contributions at every step. -/
private theorem eval_derivative_mulFold
    (q : CoefficientPolynomial K) (x : K) :
    ∀ (coefficients : List K) (accumulator : CoefficientPolynomial K)
      (value derivativeValue : K),
      accumulator.eval x = value * q.eval x →
      (derivative accumulator).eval x =
        derivativeValue * q.eval x + value * (derivative q).eval x →
      let scalarResult := coefficients.foldl (evalDerivativeStep x)
        (value, derivativeValue)
      let polynomialResult := coefficients.foldl
        (fun result coefficient => DensePolynomial.shift 1 result + DensePolynomial.scale coefficient q)
        accumulator
      polynomialResult.eval x = scalarResult.1 * q.eval x ∧
        (derivative polynomialResult).eval x =
          scalarResult.2 * q.eval x +
            scalarResult.1 * (derivative q).eval x
  | [], accumulator, value, derivativeValue, valueSpec, derivativeSpec =>
      ⟨valueSpec, derivativeSpec⟩
  | coefficient :: coefficients, accumulator, value, derivativeValue,
      valueSpec, derivativeSpec => by
      let next := DensePolynomial.shift 1 accumulator + DensePolynomial.scale coefficient q
      have nextValue : next.eval x =
          (value * x + coefficient) * q.eval x := by
        dsimp only [next]
        rw [DensePolynomial.eval_add, DensePolynomial.eval_shift, DensePolynomial.eval_scale, pow_one, valueSpec]
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

/-- Direct finite product rule for the executable Horner derivative.

The original convolution accumulator retains the fixed right factor.
Both scalar product-rule contributions are carried through that same finite fold. -/
theorem eval_derivative_mul (p q : CoefficientPolynomial K) (x : K) :
    (derivative (p * q)).eval x =
      (derivative p).eval x * q.eval x +
        p.eval x * (derivative q).eval x := by
  have result := eval_derivative_mulFold q x p.coeffs 0 0 0
    (by
      rewrite [DensePolynomial.eval_zero, zero_mul]
      exact Eq.refl _)
    (by
      rewrite [zero_mul, zero_mul, zero_add, eval_derivative]
      exact Eq.refl _)
  change (derivative (p.coeffs.foldl
    (fun accumulator coefficient =>
      DensePolynomial.shift 1 accumulator + DensePolynomial.scale coefficient q) 0)).eval x = _
  have derivativeResult := result.2
  change (derivative (p.coeffs.foldl
      (fun accumulator coefficient =>
        DensePolynomial.shift 1 accumulator + DensePolynomial.scale coefficient q) 0)).eval x =
    (evalDerivativeCoeffs x p.coeffs).2 * q.eval x +
      (evalDerivativeCoeffs x p.coeffs).1 *
        (derivative q).eval x at derivativeResult
  rw [← eval_derivative, eval_original] at derivativeResult
  exact derivativeResult

end

end Purelib.Polynomial.Dense.Derivative
