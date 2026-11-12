module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Power
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-!
# Geometric decay of the inverse-root differential equation residual

For an inverse-root polynomial Q of P, the finite differential residual is
J = 2 P Q' + P' Q. Newton refinement multiplies J by 3e/2, where e is the
cached root residual. Its squared norm therefore contracts by at least four
on the model's entire box. This controls derivatives of polynomial root
coordinates without differentiating an operational root or taking a limit.
-/

namespace Purelib.Riemann.Normalization.InverseModelDifferentialResidual

open Purelib.Riemann.Normalization.InverseModelDerivativeBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Algebra.Quadratic.Pair.Polynomial
open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense

open Purelib.Polynomial in
/-- Evaluate the inverse-root differential residual twice the parameter times the inverse derivative plus the parameter
derivative times the inverse. -/
@[expose] def differentialResidual (polynomial value : Polynomial) (point : Gaussian) : Gaussian :=
  2 * polynomial.eval point * (derivative value).eval point + (derivative
    polynomial).eval point * value.eval point

/-- Retain the finite coefficient polynomial of the inverse-root differential residual. -/
@[expose] def differentialResidualPolynomial (polynomial value : Polynomial) : Polynomial :=
  (polynomial * derivative value).scale 2 + derivative polynomial * value

/-- Read the retained residual coefficient polynomial through the original scalar residual formula. -/
theorem differentialResidualPolynomial_eval (polynomial value : Polynomial) (point : Gaussian) :
    (differentialResidualPolynomial polynomial value).eval point = differentialResidual polynomial value point := by
  simp only [differentialResidualPolynomial, DensePolynomial.eval_add, DensePolynomial.eval_scale,
    DensePolynomial.eval_mul, differentialResidual]
  ring1

/-- Retain the exact algebraic difference between one original polynomial model and its formal inverse root. -/
@[expose] def inverseModelError (polynomial value : Polynomial) : Expression polynomial :=
  (Expression.scalar value).sub (Expression.inverseRoot polynomial)

/-- The coefficient equation for one retained algebraic model error and its cached derivative. -/
@[expose] def ErrorEquation (polynomial residual : Polynomial) (error slope : Expression polynomial) : Prop :=
  ((slope.scale (polynomial.scale 2)).add (error.scale (derivative polynomial))).Equal (Expression.scalar residual)

/-- The actual polynomial differential residual is the exact algebraic inverse-root error equation.

The formal inverse-root terms cancel by their coefficient laws. The scalar
polynomial model keeps its genuine residual instead of acquiring an exact
root or derivative assertion at a finite stage. -/
theorem inverseModelError_equation (polynomial value : Polynomial) :
    ErrorEquation polynomial (differentialResidualPolynomial polynomial value)
      (inverseModelError polynomial value) (inverseModelError polynomial value).derivative := by
  unfold ErrorEquation
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [inverseModelError, Expression.derivative, Expression.directionalDerivative,
      Expression.sub, Expression.add, Expression.scale, Expression.neg, Expression.scalar,
      Expression.inverseRoot, Expression.oddReciprocal, Pair.scale,
      Pair.add_re, Pair.add_im,
      Pair.neg_re, Pair.neg_im,
      Pair.scalar_re, Pair.scalar_im,
      DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_sub, DensePolynomial.eval_neg,
      DensePolynomial.eval_scale, DensePolynomial.eval_constant, DensePolynomial.eval_zero,
      Derivative.eval_derivative_add,
      Derivative.eval_derivative_mul,
      Derivative.eval_derivative_neg,
      Power.eval_derivative_constant,
      Power.eval_derivative_power_succ,
      Power.eval_power, Power.eval_derivative_zero,
      differentialResidualPolynomial, Nat.cast_zero, pow_zero]
    ring1
  · intro point
    simp only [inverseModelError, Expression.derivative, Expression.directionalDerivative,
      Expression.sub, Expression.add, Expression.scale, Expression.neg, Expression.scalar,
      Expression.inverseRoot, Expression.oddReciprocal, Pair.scale,
      Pair.add_re, Pair.add_im,
      Pair.neg_re, Pair.neg_im,
      Pair.scalar_re, Pair.scalar_im,
      DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_sub, DensePolynomial.eval_neg,
      DensePolynomial.eval_scale, DensePolynomial.eval_constant, DensePolynomial.eval_zero,
      Derivative.eval_derivative_add,
      Derivative.eval_derivative_mul,
      Derivative.eval_derivative_neg,
      Power.eval_derivative_constant,
      Power.eval_derivative_power_succ,
      Power.eval_power, Power.eval_derivative_zero,
      differentialResidualPolynomial, Nat.cast_zero, pow_zero]
    ring1

namespace Model

variable {polynomial : Polynomial} {box : Box}

open Purelib.Riemann in
open Purelib.Polynomial in
/-- One Newton step multiplies the differential residual by three halves times the root residual. -/
theorem step_differentialResidual (model : Model polynomial box) (point : Gaussian) :
    differentialResidual polynomial model.step.value point =
      (3 * half) * model.residual.eval point * differentialResidual polynomial model.value point := by
  unfold differentialResidual
  rw [(Model.step_derivative model)]
  have value_eq : model.step.value.eval point =
      model.value.eval point * (1 + half * model.residual.eval point) := by
    change (model.value * (constant 1 + model.residual.scale half)).eval point = _
    rw [eval_mul, eval_add,
      eval_constant, eval_scale]
  rw [value_eq]
  calc
    _ = (3 * half) * model.residual.eval point *
        (2 * polynomial.eval point * (derivative model.value).eval point +
          (derivative polynomial).eval point * model.value.eval point) +
        (1 - 2 * half) * (derivative polynomial).eval point * model.value.eval point := by
      rw [model.residual_eq]
      ring1
    _ = _ := by rw [show (2 : Gaussian) * half = 1 by decide]; ring1

/-- Derive the exact mismatch between an odd-power polynomial primitive and
the corresponding algebraic differential model.

The retained Newton model remains inexact. Its original square residual and
differential residual account for the whole mismatch; neither residual is
replaced by zero at a finite refinement stage.
-/
theorem primitive_differentialResidual (model : Model polynomial box) (numerator : Polynomial)
    (index : Nat) (point : Gaussian) :
    let coefficient := 2 * polynomial.eval point * (derivative numerator).eval point -
      ((index : Gaussian) + 1) * numerator.eval point * (derivative polynomial).eval point
    2 * polynomial.eval point *
      ((derivative (numerator * Power.power model.value (index + 1))).eval point -
        half * coefficient * model.value.eval point ^ (index + 3)) =
      coefficient * model.value.eval point ^ (index + 1) * model.residual.eval point +
        ((index : Gaussian) + 1) * numerator.eval point * model.value.eval point ^ index *
          differentialResidual polynomial model.value point := by
  dsimp only
  rewrite [Derivative.eval_derivative_mul,
    Power.eval_power,
    Power.eval_derivative_power_succ, model.residual_eq]
  unfold differentialResidual
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide
  simp only [pow_succ]
  calc
    _ = (2 * polynomial.eval point * (derivative numerator).eval point -
        ((index : Gaussian) + 1) * numerator.eval point * (derivative polynomial).eval point) *
        (model.value.eval point ^ index * model.value.eval point) *
          (1 - polynomial.eval point * (model.value.eval point * model.value.eval point)) +
        ((index : Gaussian) + 1) * numerator.eval point * model.value.eval point ^ index *
          (2 * polynomial.eval point * (derivative model.value).eval point +
            (derivative polynomial).eval point * model.value.eval point) +
        (1 - 2 * half) * polynomial.eval point *
          (2 * polynomial.eval point * (derivative numerator).eval point -
            ((index : Gaussian) + 1) * numerator.eval point * (derivative polynomial).eval point) *
          (model.value.eval point ^ index * model.value.eval point * model.value.eval point *
            model.value.eval point) := by ring1
    _ = _ := by rewrite [twiceHalf]; ring1

open Purelib.Riemann in
open Purelib.Data in
/-- One Newton step contracts the squared differential residual by at least a factor of four inside the model box. -/
theorem step_differentialResidual_bound (model : Model polynomial box) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (differentialResidual polynomial model.step.value point) ≤
      normSq (differentialResidual polynomial model.value point) / 4 := by
  rw [(step_differentialResidual model),
    normSq_mul, normSq_mul,
    show normSq ((3 : Gaussian) * half) = (9 / 4 : Coordinate) by decide +kernel]
  calc
    _ ≤ ((9 / 4 : Coordinate) * (1 / 16)) * normSq (differentialResidual polynomial model.value point) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          ((model.residualBound point inside).trans model.bound_small) (by decide +kernel))
            (normSq_nonneg _)
    _ ≤ (1 / 4 : Coordinate) * normSq (differentialResidual polynomial model.value point) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (normSq_nonneg _)
    _ = _ := by
      simp only [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul]
      ring1

end Model

set_option genInjectivity false in
open Purelib.Polynomial in
/-- A cached polynomial for the initial differential residual and its finite norm ceiling.

The evaluation identity binds the polynomial to the exact model; the bound is the coefficient estimate on that model's
box. -/
structure DifferentialResidualBounds {polynomial : Polynomial} {box : Box} (model : Model polynomial box) where
  /-- The retained differential-residual polynomial. -/ value : Polynomial
  /-- Evaluation equals the exact model's differential residual at every point. -/ value_eq : ∀ point, value.eval point
    = differentialResidual polynomial model.value point
  /-- The cached finite squared-norm ceiling. -/ bound : Coordinate
  /-- The ceiling is the exact coefficient bound on the retained model box. -/ bound_eq : bound =
    Dense.Gaussian.Bounds.Box.denseEvalNormBound value box
  /-- The retained exact error uses the same original polynomial model and formal inverse root. -/
  exactError : Expression polynomial
  /-- The retained error is the canonical original-model error expression. -/
  exactError_eq : exactError = inverseModelError polynomial model.value
  /-- The cached formal derivative of that same error expression. -/
  exactDerivative : Expression polynomial
  /-- The derivative was computed from the retained original error expression. -/
  exactDerivative_eq : exactDerivative = exactError.derivative
  /-- The cached residual is the exact finite coefficient error equation. -/
  errorEquation : ErrorEquation polynomial value exactError exactDerivative

constructive_injectivity DifferentialResidualBounds

namespace DifferentialResidualBounds

variable {polynomial : Polynomial} {box : Box} {model : Model polynomial box}

section
open Purelib.Polynomial
/-- Compute the differential-residual polynomial and cache its box norm bound. -/
@[expose] def build (model : Model polynomial box) : DifferentialResidualBounds model :=
  let value := differentialResidualPolynomial polynomial model.value
  let error := inverseModelError polynomial model.value
  let slope := error.derivative
  ⟨value, differentialResidualPolynomial_eval polynomial model.value,
    Dense.Gaussian.Bounds.Box.denseEvalNormBound value box, rfl,
    error, rfl, slope, rfl, inverseModelError_equation polynomial model.value⟩

/-- The cached differential-residual ceiling is nonnegative. -/
theorem bound_nonnegative (bounds : DifferentialResidualBounds model) : 0 ≤ bounds.bound := by
  rw [bounds.bound_eq]
  exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg _ _).1

end

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Bound every refined differential residual by the geometric quarter-radius of the initial cache.

The point remains inside the original model box, and each exact Newton step preserves the same retained refinement
chain. -/
theorem refine_bound (bounds : DifferentialResidualBounds model) (index : Nat) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (differentialResidual polynomial (model.refine index).value point) ≤ quarterRadius
      bounds.bound index := by
  induction index with
  | zero =>
      change normSq (differentialResidual polynomial model.value point) ≤ quarterRadius
        bounds.bound 0
      rw [← bounds.value_eq, Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Rat.Fraction.Field.mul_one_direct, bounds.bound_eq]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound bounds.value inside
  | succ index previous =>
      change normSq (differentialResidual polynomial (model.refine index).step.value point) ≤ _
      apply ((Model.step_differentialResidual_bound (model.refine index))
        inside).trans
      calc
        _ = normSq (differentialResidual polynomial (model.refine index).value point) * (1 / 4 : Coordinate) := by
          simp only [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul, -eq_self, -iff_self]
          rfl
        _ ≤ quarterRadius bounds.bound index * (1 / 4 : Coordinate) :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct previous (by decide)
        _ = _ := by
          rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
            pow_succ]
          ring1

end DifferentialResidualBounds
end Purelib.Riemann.Normalization.InverseModelDifferentialResidual
