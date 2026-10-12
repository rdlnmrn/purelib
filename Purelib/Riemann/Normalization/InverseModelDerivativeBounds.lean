module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Polynomial.Dense.Derivative
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds

/-!
# Derivative bounds independent of the inverse-model refinement index

The derivative of the Newton correction contracts its inherited derivative
term by the small residual. The forcing term uses only the fixed derivative
of the curve polynomial and the clearance's uniform inverse-model ceiling.
Thus polynomial degree growth does not force a larger spatial error budget.
All differentiation and identity checks concern finite coefficient lists.
-/

open Purelib.Data.Gaussian in
/-- The canonical Gaussian squared norm of a natural power equals the same power of the original squared norm. -/
private theorem canonicalNormSqPow (source :
  Basic.Canonical) (exponent : Nat) :
    Basic.Canonical.normSq (source ^ exponent) = Basic.Canonical.normSq source ^ exponent := by
  simpa only [Norm.Basic.normSq_eq_canonical] using Power.normSq_pow source exponent

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds

section

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative (derivative)

section

variable {polynomial : Polynomial} {box : Box}

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds.Model

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Differentiate the retained inverse-root correction step into its residual-weighted inherited derivative and cubic
forcing term.

The identity concerns exact evaluations of the original model and polynomial derivatives, with the original half
coefficient and residual polynomial retained. -/
theorem step_derivative (model : Model polynomial box) (point : Gaussian) :
    (Dense.Derivative.derivative model.step.value).eval point =
      (3 * half) * model.residual.eval point * (Dense.Derivative.derivative model.value).eval point -
        half * (Dense.Derivative.derivative polynomial).eval point * (model.value.eval point) ^ 3 := by
  let formula := (model.value.scale 3 - polynomial * model.value * model.value * model.value).scale half
  have same : (model.step.value - formula).isZero = true := by
    apply NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro sample _
    change (model.value * (Dense.Basic.DensePolynomial.constant 1 + model.residual.scale half)).eval sample =
      formula.eval sample
    simp only [formula, Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add,
      Dense.Basic.DensePolynomial.eval_sub, Dense.Basic.DensePolynomial.eval_scale,
      Dense.Basic.DensePolynomial.eval_constant, model.residual_eq]
    calc
      _ = half * (3 * model.value.eval sample - polynomial.eval sample * model.value.eval sample *
          model.value.eval sample * model.value.eval sample) + (1 - 2 * half) * model.value.eval sample := by ring1
      _ = _ := by rw [show (2 : Gaussian) * half = 1 by decide]; ring1
  rw [Dense.Derivative.eval_derivative_eq_of_sub_isZero same point]
  simp only [formula, Dense.Derivative.eval_derivative_scale, Dense.Derivative.eval_derivative_sub,
    Dense.Derivative.eval_derivative_mul, Dense.Basic.DensePolynomial.eval_mul, model.residual_eq]
  ring1

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds.Model

end

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached polynomial and initial-model derivatives with a uniform squared-norm bound for every inverse-root refinement
derivative.

The cache retains the exact derivative evaluation equations and box majorants; its bound is the initial derivative
majorant plus the polynomial derivative majorant times the inverse-model majorant cubed. -/
structure DerivativeBounds {polynomial : Polynomial} {box : Box}
    (clearance : RegionClearance polynomial box) (initial : Model polynomial box) where
  /-- The cached derivative polynomial of the original denominator polynomial. -/ polynomialDerivative : Polynomial
  /-- The cache agrees pointwise with the exact original polynomial derivative. -/ polynomialDerivative_eq : ∀ point,
    polynomialDerivative.eval point = (Dense.Derivative.derivative polynomial).eval point
  /-- The cached derivative polynomial of the original initial inverse-root model. -/ initialDerivative : Polynomial
  /-- The cache agrees pointwise with the exact original model derivative. -/ initialDerivative_eq : ∀ point,
    initialDerivative.eval point = (Dense.Derivative.derivative initial.value).eval point
  /-- The cached box squared-norm majorant for the original polynomial derivative. -/ polynomialUpper :
    Fraction.Rational
  /-- This majorant equals the dense box evaluation bound of the cached polynomial derivative. -/ polynomialUpper_eq :
    polynomialUpper = Bounds.Box.denseEvalNormBound polynomialDerivative box
  /-- The cached box squared-norm majorant for the initial model derivative. -/ initialUpper : Fraction.Rational
  /-- This majorant equals the dense box evaluation bound of the cached initial derivative. -/ initialUpper_eq :
    initialUpper = Bounds.Box.denseEvalNormBound initialDerivative box
  /-- The cached squared-norm majorant for valid inverse-root model values. -/ inverseUpper : Fraction.Rational
  /-- The inverse majorant equals one plus four divided by the original clearance bound. -/ inverseUpper_eq :
    inverseUpper = 1 + 4 / clearance.bound
  /-- The cached uniform squared-norm bound on all refinement derivatives. -/ bound : Fraction.Rational
  /-- The total bound is the initial derivative majorant plus the polynomial derivative majorant times the cubed inverse
    majorant. -/ bound_eq : bound = initialUpper + polynomialUpper * inverseUpper ^ 3

constructive_injectivity DerivativeBounds

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds

section

variable {polynomial : Polynomial} {box : Box} {clearance : RegionClearance polynomial box}
  {initial : Model polynomial box}

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cache the original polynomial and initial-model derivatives, box majorants and uniform refinement derivative bound.
-/
@[expose] def build (clearance : RegionClearance polynomial box) (initial : Model polynomial box) : DerivativeBounds
  clearance initial :=
  let polynomialDerivative := Dense.Derivative.derivative polynomial
  let initialDerivative := Dense.Derivative.derivative initial.value
  let polynomialUpper := Bounds.Box.denseEvalNormBound polynomialDerivative box
  let initialUpper := Bounds.Box.denseEvalNormBound initialDerivative box
  let inverseUpper := 1 + 4 / clearance.bound
  ⟨polynomialDerivative, fun _ => rfl, initialDerivative, fun _ => rfl,
    polynomialUpper, rfl, initialUpper, rfl, inverseUpper, rfl, initialUpper + polynomialUpper * inverseUpper ^ 3, rfl⟩

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

section
open Purelib.Polynomial.Dense.Gaussian

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

/-- The cached original polynomial derivative squared-norm majorant is nonnegative. -/
theorem polynomialUpper_nonnegative (bounds : DerivativeBounds clearance initial) : 0 ≤ bounds.polynomialUpper := by
  rw [bounds.polynomialUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The cached initial-model derivative squared-norm majorant is nonnegative. -/
theorem initialUpper_nonnegative (bounds : DerivativeBounds clearance initial) : 0 ≤ bounds.initialUpper := by
  rw [bounds.initialUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

end

namespace Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

open Purelib.Polynomial in
/-- The retained inverse-model squared-norm majorant is strictly positive. -/
theorem inverseUpper_positive (bounds : DerivativeBounds clearance initial) : 0 < bounds.inverseUpper := by
  rw [bounds.inverseUpper_eq]
  exact (PrimitiveOverlapBounds.build clearance (Dense.Basic.DensePolynomial.constant 1)).inverseUpper_positive

open Purelib.Data.Rat in
/-- The cached uniform refinement derivative bound is nonnegative. -/
theorem bound_nonnegative (bounds : DerivativeBounds clearance initial) : 0 ≤ bounds.bound := by
  rw [bounds.bound_eq]
  exact add_nonneg bounds.initialUpper_nonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct
    bounds.polynomialUpper_nonnegative (Fraction.Order.Arithmetic.pow_nonneg_direct bounds.inverseUpper_positive.le 3))

/-- The polynomial-derivative forcing majorant is no larger than the retained total derivative bound. -/
theorem forcing_le (bounds : DerivativeBounds clearance initial) : bounds.polynomialUpper * bounds.inverseUpper ^ 3 ≤
  bounds.bound := by
  rw [bounds.bound_eq]
  exact le_add_of_nonneg_left bounds.initialUpper_nonnegative

open Purelib.Polynomial in
/-- Every valid inverse-root model value in the original cleared box satisfies the retained inverse-model majorant. -/
theorem value_le (bounds : DerivativeBounds clearance initial) (model : Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) : normSq (model.value.eval point) ≤ bounds.inverseUpper := by
  rw [bounds.inverseUpper_eq]
  exact (PrimitiveOverlapBounds.build clearance (Dense.Basic.DensePolynomial.constant 1)).inverse_norm_le model inside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Normalization in
/-- Every refinement of the original inverse-root model satisfies the same retained derivative squared-norm bound
throughout its box.

The correction derivative splits into inherited and forcing terms; the original residual bound makes their combined
estimate contract within the cached uniform bound. -/
theorem refine_derivative_le (bounds : DerivativeBounds clearance initial) (index : Nat)
    {point : Gaussian} (inside : box.Contains point) :
    normSq ((Dense.Derivative.derivative (initial.refine index).value).eval point) ≤ bounds.bound := by
  induction index with
  | zero =>
      change normSq ((Dense.Derivative.derivative initial.value).eval point) ≤ _
      rw [← bounds.initialDerivative_eq]
      have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound bounds.initialDerivative inside
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact (scalar.trans_eq bounds.initialUpper_eq.symm).trans (by
          rw [bounds.bound_eq]
          exact le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.polynomialUpper_nonnegative
            (Fraction.Order.Arithmetic.pow_nonneg_direct bounds.inverseUpper_positive.le 3)))
  | succ index ih =>
      let model := initial.refine index
      have polynomialLe : normSq ((Dense.Derivative.derivative polynomial).eval point) ≤ bounds.polynomialUpper := by
        rw [← bounds.polynomialDerivative_eq]
        have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound bounds.polynomialDerivative inside
        rw [Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar.trans_eq bounds.polynomialUpper_eq.symm
      have residualLe := (model.residualBound point inside).trans model.bound_small
      have inherited : normSq ((3 * half) * model.residual.eval point * (Dense.Derivative.derivative model.value).eval
        point) ≤
          (9 / 64 : Fraction.Rational) * bounds.bound := by
        rw [Basic.Canonical.normSq_mul, Basic.Canonical.normSq_mul, show normSq ((3 : Gaussian) * half) = (9 / 4 :
          Fraction.Rational) by decide +kernel]
        exact (Fraction.Order.Arithmetic.mul_le_mul_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct residualLe (by decide +kernel)) ih
          (Basic.Canonical.normSq_nonneg _) (by decide +kernel)).trans_eq (by
            rw [show (9 / 4 : Fraction.Rational) * (1 / 16) = 9 / 64 by decide +kernel])
      have forcing : normSq (half * (Dense.Derivative.derivative polynomial).eval point * (model.value.eval point) ^ 3)
        ≤
          (1 / 4 : Fraction.Rational) * bounds.bound := by
        rw [Basic.Canonical.normSq_mul, Basic.Canonical.normSq_mul, canonicalNormSqPow,
          show normSq half = (1 / 4 : Fraction.Rational) by decide +kernel]
        calc
          _ ≤ ((1 / 4 : Fraction.Rational) * bounds.polynomialUpper) * bounds.inverseUpper ^ 3 :=
            Fraction.Order.Arithmetic.mul_le_mul_direct
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct polynomialLe (by decide))
              (Fraction.Order.Arithmetic.pow_le_pow_direct (Basic.Canonical.normSq_nonneg _) (bounds.value_le model
                inside) 3)
              (Fraction.Order.Arithmetic.pow_nonneg_direct (Basic.Canonical.normSq_nonneg _) 3)
              (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.polynomialUpper_nonnegative)
          _ = (1 / 4 : Fraction.Rational) * (bounds.polynomialUpper * bounds.inverseUpper ^ 3) := by ring1
          _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounds.forcing_le (by decide)
      change normSq ((Dense.Derivative.derivative model.step.value).eval point) ≤ _
      rw [(Purelib.Riemann.Normalization.InverseModelDerivativeBounds.Model.step_derivative model)]
      calc
        _ ≤ 2 * (normSq ((3 * half) * model.residual.eval point * (Dense.Derivative.derivative model.value).eval point)
          +
            normSq (half * (Dense.Derivative.derivative polynomial).eval point * (model.value.eval point) ^ 3)) := by
              simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Bounds.normSq_sub_le_two _ _
        _ ≤ 2 * ((9 / 64 : Fraction.Rational) * bounds.bound + (1 / 4 : Fraction.Rational) * bounds.bound) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add inherited forcing) (by decide)
        _ = (2 * (9 / 64 + 1 / 4) : Fraction.Rational) * bounds.bound := by ring1
        _ = (25 / 32 : Fraction.Rational) * bounds.bound := by
          rw [show (2 * (9 / 64 + 1 / 4) : Fraction.Rational) = 25 / 32 by decide +kernel]
        _ ≤ 1 * bounds.bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
          bounds.bound_nonnegative
        _ = _ := Fraction.Field.one_mul _

end Purelib.Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds

end

end
