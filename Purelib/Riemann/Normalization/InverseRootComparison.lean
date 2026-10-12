module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

public import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite comparison with a selected approximate root

A quadratic residual does not distinguish opposite sheets.  The additional
quantity `1 - root * value` does: it is small only near the inverse of the
displayed root.  Newton refinement preserves this initial alignment and has
an explicit finite comparison rate, including the displayed root's residual.

These lemmas do not assume an exact or completed square root.  Acquiring the
initial alignment from a continued owner is a separate geometric obligation.
-/

namespace Purelib.Riemann.Normalization.InverseRootComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data
/-- Small inverse-root residual bounds parameter quadrance times squared value quadrance by four. -/
theorem normalized_value_bound {parameter value : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq (1 - parameter * value ^ 2) <= 1 / 16) :
    Gaussian.Norm.Basic.normSq parameter * Gaussian.Norm.Basic.normSq value ^ 2 <= 4 := by
  have identity : parameter * value ^ 2 = 1 - (1 - parameter * value ^ 2) := by ring1
  calc
    _ = Gaussian.Norm.Basic.normSq (parameter * value ^ 2) := by
      rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow]
    _ = Gaussian.Norm.Basic.normSq (1 - (1 - parameter * value ^ 2)) := congrArg
      Gaussian.Norm.Basic.normSq identity
    _ <= 2 * (Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) + Gaussian.Norm.Basic.normSq
      (1 - parameter * value ^ 2)) :=
      Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ <= 2 * (1 + 1) := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (le_of_eq (by decide)) (small.trans (by decide))) (by decide)
    _ = 4 := by decide

/-- The Newton correction splits alignment mismatch into a quadratic term and the selected root's residual. -/
theorem correction_mismatch (parameter value root : Gaussian.Basic.Canonical) :
    1 - root * correction value (1 - parameter * value ^ 2) =
      (1 - root * value) ^ 2 * (3 - (1 - root * value)) * half -
        (root ^ 2 - parameter) * value ^ 2 * (1 - (1 - root * value)) * half := by
  have twice : (2 : Gaussian.Basic.Canonical) * half = 1 := by decide
  calc
    _ = (1 - root * value) ^ 2 * (3 - (1 - root * value)) * half -
        (root ^ 2 - parameter) * value ^ 2 * (1 - (1 - root * value)) * half +
        (1 - 2 * half) * (1 - root * value) := by unfold correction; ring1
    _ = _ := by rw [twice]; ring1

/-- An alignment mismatch of quadrance at most 1/64 gives quarter contraction of the quadratic term. -/
private theorem mismatch_quadratic_bound {mismatch : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq mismatch <= 1 / 64) :
    2 * Gaussian.Norm.Basic.normSq (mismatch ^ 2 * (3 - mismatch) * half) <=
      Gaussian.Norm.Basic.normSq mismatch / 4 := by
  have nonnegative := Gaussian.Norm.Basic.normSq_nonneg mismatch
  have factorBound : Gaussian.Norm.Basic.normSq ((3 : Gaussian.Basic.Canonical) - mismatch) <= 20 := by
    calc
      _ <= 2 * (Gaussian.Norm.Basic.normSq (3 : Gaussian.Basic.Canonical) + Gaussian.Norm.Basic.normSq
        mismatch) := Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ <= 2 * (9 + 1) := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_of_eq (by decide)) (small.trans (by decide +kernel))) (by decide)
      _ = 20 := by decide
  have scaledSmall : Gaussian.Norm.Basic.normSq mismatch * 64 <= 1 :=
    (Rat.Fraction.Order.Field.le_div_iff_pos (by decide +kernel : (0 : Rat.Fraction.Rational) < 64)).1 small
  have scaleBound : Gaussian.Norm.Basic.normSq mismatch ^ 2 * 64 <= Gaussian.Norm.Basic.normSq
    mismatch := by
    calc
      _ = Gaussian.Norm.Basic.normSq mismatch * (Gaussian.Norm.Basic.normSq mismatch * 64) := by ring1
      _ <= Gaussian.Norm.Basic.normSq mismatch * 1 :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scaledSmall nonnegative
      _ = Gaussian.Norm.Basic.normSq mismatch := Rat.Fraction.Field.mul_one_direct _
  calc
    _ = 2 * (Gaussian.Norm.Basic.normSq mismatch ^ 2 * Gaussian.Norm.Basic.normSq (3 - mismatch) * (1
      / 4)) := by
      rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, show
        Gaussian.Norm.Basic.normSq half = (1 / 4 : Rat.Fraction.Rational) by decide]
    _ <= 2 * (Gaussian.Norm.Basic.normSq mismatch ^ 2 * 20 * (1 / 4)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorBound
            (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)) (by decide)) (by decide)
    _ = Gaussian.Norm.Basic.normSq mismatch ^ 2 * 10 := by
      have scalar : (2 : Rat.Fraction.Rational) * 20 * (1 / 4) = 10 := by decide +kernel
      calc
        _ = Gaussian.Norm.Basic.normSq mismatch ^ 2 * (2 * 20 * (1 / 4)) := by ring1
        _ = _ := by rw [scalar]
    _ <= Gaussian.Norm.Basic.normSq mismatch ^ 2 * 16 :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = (Gaussian.Norm.Basic.normSq mismatch ^ 2 * 64) / 4 := by
      have scalar : (64 : Rat.Fraction.Rational) / 4 = 16 := by decide +kernel
      rw [Rat.Fraction.Field.div_eq_mul_inv_direct] at scalar ⊢
      calc
        _ = Gaussian.Norm.Basic.normSq mismatch ^ 2 * (64 * (4 : Rat.Fraction.Rational)⁻¹) := by rw [scalar]
        _ = _ := by ring1
    _ <= Gaussian.Norm.Basic.normSq mismatch / 4 := by
      simpa only [Rat.Fraction.Field.div_eq_mul_inv_direct] using
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaleBound
          (by decide : (0 : Rat.Fraction.Rational) <= (4 : Rat.Fraction.Rational)⁻¹)

/-- One Newton correction contracts the selected-root mismatch with an explicit residual allowance.

The initial inverse-root residual and sign-sensitive mismatch obey their smallness bounds. The new mismatch quadrance is
at most one quarter of the old value plus eight times the nonnegative relative root error. -/
theorem correction_mismatch_bound {parameter value root : Gaussian.Basic.Canonical} {rootError : Rat.Fraction.Rational}
    (rootErrorNonnegative : 0 <= rootError)
    (rootResidual : Gaussian.Norm.Basic.normSq (root ^ 2 - parameter) <= rootError *
      Gaussian.Norm.Basic.normSq parameter)
    (residualSmall : Gaussian.Norm.Basic.normSq (1 - parameter * value ^ 2) <= 1 / 16)
    (mismatchSmall : Gaussian.Norm.Basic.normSq (1 - root * value) <= 1 / 64) :
    Gaussian.Norm.Basic.normSq (1 - root * correction value (1 - parameter * value ^ 2)) <=
      Gaussian.Norm.Basic.normSq (1 - root * value) / 4 + 8 * rootError := by
  let mismatch := 1 - root * value
  have normalized := normalized_value_bound residualSmall
  have residualValue : Gaussian.Norm.Basic.normSq (root ^ 2 - parameter) * Gaussian.Norm.Basic.normSq
    value ^ 2 <= 4 * rootError := by
    calc
      _ <= (rootError * Gaussian.Norm.Basic.normSq parameter) * Gaussian.Norm.Basic.normSq value ^ 2
        :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rootResidual
          (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = rootError * (Gaussian.Norm.Basic.normSq parameter * Gaussian.Norm.Basic.normSq value ^ 2) :=
        by
        ring1
      _ <= rootError * 4 := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        normalized rootErrorNonnegative
      _ = 4 * rootError := by ring1
  have factorBound : Gaussian.Norm.Basic.normSq (1 - mismatch) <= 4 := by
    calc
      _ <= 2 * (Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) + Gaussian.Norm.Basic.normSq
        mismatch) := Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ <= 2 * (1 + 1) := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_of_eq (by decide)) (mismatchSmall.trans (by decide +kernel))) (by decide)
      _ = 4 := by decide
  have perturbation :
      Gaussian.Norm.Basic.normSq ((root ^ 2 - parameter) * value ^ 2 * (1 - mismatch) * half) <= 4 * rootError
        := by
    rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow,
      show Gaussian.Norm.Basic.normSq half = (1 / 4 : Rat.Fraction.Rational) by decide]
    calc
      _ <= (4 * rootError) * 4 * (1 / 4) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct residualValue factorBound
            (Gaussian.Norm.Basic.normSq_nonneg _) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              rootErrorNonnegative))
          (by decide)
      _ = (4 * rootError) * (4 * (1 / 4)) := by ring1
      _ = 4 * rootError := by
        rw [show (4 : Rat.Fraction.Rational) * (1 / 4) = 1 by decide, Rat.Fraction.Field.mul_one_direct]
  rw [correction_mismatch]
  calc
    _ <= 2 * (Gaussian.Norm.Basic.normSq (mismatch ^ 2 * (3 - mismatch) * half) +
        Gaussian.Norm.Basic.normSq ((root ^ 2 - parameter) * value ^ 2 * (1 - mismatch) * half)) :=
          Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ = 2 * Gaussian.Norm.Basic.normSq (mismatch ^ 2 * (3 - mismatch) * half) +
        2 * Gaussian.Norm.Basic.normSq ((root ^ 2 - parameter) * value ^ 2 * (1 - mismatch) * half) := by ring1
    _ <= Gaussian.Norm.Basic.normSq mismatch / 4 + 2 * (4 * rootError) := add_le_add
      (mismatch_quadratic_bound mismatchSmall)
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct perturbation (by decide))
    _ = Gaussian.Norm.Basic.normSq (1 - root * value) / 4 + 8 * rootError := by dsimp only [mismatch]; ring1

end

namespace Model

variable {polynomial : Polynomial} {box : Box}

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Every finite refinement retains the selected approximate root's alignment bound.

The initial bound plus sixteen times relative root error is at most 1/64. The Newton contribution decays
quarter-geometrically, while the retained sample's residual contributes the fixed sixteen-error allowance. -/
theorem refine_mismatch_bound (model : Model polynomial box) (point : Gaussian.Basic.Canonical)
    (inside : box.Contains point) (root : Gaussian.Basic.Canonical) {initialBound rootError : Rat.Fraction.Rational}
    (rootErrorNonnegative : 0 <= rootError)
    (rootResidual : Gaussian.Norm.Basic.normSq (root ^ 2 - polynomial.eval point) <= rootError *
      Gaussian.Norm.Basic.normSq (polynomial.eval point))
    (initial : Gaussian.Norm.Basic.normSq (1 - root * model.value.eval point) <= initialBound)
    (budgetSmall : initialBound + 16 * rootError <= 1 / 64) (index : Nat) :
    Gaussian.Norm.Basic.normSq (1 - root * (model.refine index).value.eval point) <=
      Rational.Geometric.Basic.quarterRadius initialBound index + 16 * rootError := by
  have initialNonnegative := (Gaussian.Norm.Basic.normSq_nonneg _).trans initial
  have noiseNonnegative : 0 <= 16 * rootError :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) rootErrorNonnegative
  induction index with
  | zero =>
      simpa only [Normalization.InverseRootPolynomial.Model.refine,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Rat.Fraction.Field.mul_one_direct] using initial.trans (le_add_of_nonneg_right noiseNonnegative)
  | succ index inductionHypothesis =>
      have small : Gaussian.Norm.Basic.normSq (1 - root * (model.refine index).value.eval point) <= 1 / 64 :=
        inductionHypothesis.trans ((add_le_add
          (Rational.Geometric.Basic.quarterRadius_le_scale initialNonnegative index) le_rfl).trans budgetSmall)
      have valueEq : (model.refine (index + 1)).value.eval point =
          correction ((model.refine index).value.eval point)
            (1 - polynomial.eval point * ((model.refine index).value.eval point) ^ 2) := by
        change ((model.refine index).value *
          (Dense.Basic.DensePolynomial.constant 1 + (model.refine index).residual.scale half)).eval point =
          correction ((model.refine index).value.eval point)
            (1 - polynomial.eval point * ((model.refine index).value.eval point) ^ 2)
        rewrite [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add,
          Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_scale,
          (model.refine index).residual_eq point]
        exact Eq.refl _
      rw [valueEq]
      have singleStep := correction_mismatch_bound rootErrorNonnegative rootResidual
        (by rw [<- (model.refine index).residual_eq]; exact
          by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
            ((model.refine index).residualBound point inside).trans (model.refine index).bound_small) small
      have divided := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inductionHypothesis
        (by decide : (0 : Rat.Fraction.Rational) <= (4 : Rat.Fraction.Rational)⁻¹)
      have noiseBound : 12 * rootError <= 16 * rootError :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) rootErrorNonnegative
      calc
        _ <= Gaussian.Norm.Basic.normSq (1 - root * (model.refine index).value.eval point) / 4 + 8 * rootError
          := singleStep
        _ <= (Rational.Geometric.Basic.quarterRadius initialBound index + 16 * rootError) / 4 + 8 * rootError :=
          add_le_add (by simpa only [Rat.Fraction.Field.div_eq_mul_inv_direct] using divided) le_rfl
        _ = Rational.Geometric.Basic.quarterRadius initialBound (index + 1) + 12 * rootError := by
          have scalar : (16 : Rat.Fraction.Rational) * (4 : Rat.Fraction.Rational)⁻¹ = 4 := by decide
          simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ,
            Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul]
          calc
            _ = initialBound * ((1 : Rat.Fraction.Rational) * (4 : Rat.Fraction.Rational)⁻¹) ^ index * (4 :
              Rat.Fraction.Rational)⁻¹ +
                ((16 * (4 : Rat.Fraction.Rational)⁻¹) + 8) * rootError := by ring1
            _ = _ := by rw [scalar]; ring1
        _ <= _ := add_le_add le_rfl noiseBound

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Convert finite sign-sensitive refinement control into error against the selected root's inverse.

The selected sample is nonzero and satisfies the displayed residual and initial alignment bounds. Divide the geometric
mismatch bound plus retained residual allowance by that sample's quadrance. -/
theorem refine_inverse_error (model : Model polynomial box) (point : Gaussian.Basic.Canonical)
    (inside : box.Contains point) (root : Gaussian.Basic.Canonical) (rootNonzero : root ≠ 0)
    {initialBound rootError : Rat.Fraction.Rational} (rootErrorNonnegative : 0 <= rootError)
    (rootResidual : Gaussian.Norm.Basic.normSq (root ^ 2 - polynomial.eval point) <= rootError *
      Gaussian.Norm.Basic.normSq (polynomial.eval point))
    (initial : Gaussian.Norm.Basic.normSq (1 - root * model.value.eval point) <= initialBound)
    (budgetSmall : initialBound + 16 * rootError <= 1 / 64) (index : Nat) :
    Gaussian.Norm.Basic.normSq ((model.refine index).value.eval point - Gaussian.Field.inv root) <=
      (Rational.Geometric.Basic.quarterRadius initialBound index + 16 * rootError) / Gaussian.Norm.Basic.normSq
        root := by
  apply (Rat.Fraction.Order.Field.le_div_iff_pos (Gaussian.Norm.Basic.normSq_pos rootNonzero)).2
  rw [<- Gaussian.Norm.Basic.normSq_mul]
  have identity : ((model.refine index).value.eval point - Gaussian.Field.inv root) * root =
      -(1 - root * (model.refine index).value.eval point) := by
    calc
      _ = root * (model.refine index).value.eval point - root * Gaussian.Field.inv root := by ring1
      _ = _ := by rw [Gaussian.Field.mul_inv root rootNonzero]; ring1
  rw [identity, Gaussian.Norm.Basic.normSq_neg]
  exact Normalization.InverseRootComparison.Model.refine_mismatch_bound model point inside root
    rootErrorNonnegative rootResidual initial budgetSmall index

end Model

end Purelib.Riemann.Normalization.InverseRootComparison
