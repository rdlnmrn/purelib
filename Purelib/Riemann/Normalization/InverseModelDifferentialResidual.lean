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
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Polynomial in
/-- Evaluate the inverse-root differential residual twice the parameter times the inverse derivative plus the parameter
derivative times the inverse. -/
@[expose] def differentialResidual (polynomial value : Polynomial) (point : Gaussian) : Gaussian :=
  2 * polynomial.eval point * (Dense.Derivative.derivative value).eval point + (Dense.Derivative.derivative
    polynomial).eval point * value.eval point

namespace Model

variable {polynomial : Polynomial} {box : Box}

open Purelib.Riemann in
open Purelib.Polynomial in
/-- One Newton step multiplies the differential residual by three halves times the root residual. -/
theorem step_differentialResidual (model : Model polynomial box) (point : Gaussian) :
    differentialResidual polynomial model.step.value point =
      (3 * half) * model.residual.eval point * differentialResidual polynomial model.value point := by
  unfold differentialResidual
  rw [(Normalization.InverseModelDerivativeBounds.Model.step_derivative model)]
  have value_eq : model.step.value.eval point =
      model.value.eval point * (1 + half * model.residual.eval point) := by
    change (model.value * (Dense.Basic.DensePolynomial.constant 1 + model.residual.scale half)).eval point = _
    rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add,
      Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_scale]
  rw [value_eq]
  calc
    _ = (3 * half) * model.residual.eval point *
        (2 * polynomial.eval point * (Dense.Derivative.derivative model.value).eval point +
          (Dense.Derivative.derivative polynomial).eval point * model.value.eval point) +
        (1 - 2 * half) * (Dense.Derivative.derivative polynomial).eval point * model.value.eval point := by
      rw [model.residual_eq]
      ring1
    _ = _ := by rw [show (2 : Gaussian) * half = 1 by decide]; ring1

open Purelib.Riemann in
open Purelib.Data in
/-- One Newton step contracts the squared differential residual by at least a factor of four inside the model box. -/
theorem step_differentialResidual_bound (model : Model polynomial box) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (differentialResidual polynomial model.step.value point) ≤
      normSq (differentialResidual polynomial model.value point) / 4 := by
  rw [(Normalization.InverseModelDifferentialResidual.Model.step_differentialResidual model),
    Gaussian.Basic.Canonical.normSq_mul, Gaussian.Basic.Canonical.normSq_mul,
    show normSq ((3 : Gaussian) * half) = (9 / 4 : Coordinate) by decide +kernel]
  calc
    _ ≤ ((9 / 4 : Coordinate) * (1 / 16)) * normSq (differentialResidual polynomial model.value point) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          ((model.residualBound point inside).trans model.bound_small) (by decide +kernel))
            (Gaussian.Basic.Canonical.normSq_nonneg _)
    _ ≤ (1 / 4 : Coordinate) * normSq (differentialResidual polynomial model.value point) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (Gaussian.Basic.Canonical.normSq_nonneg _)
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

constructive_injectivity DifferentialResidualBounds

namespace DifferentialResidualBounds

variable {polynomial : Polynomial} {box : Box} {model : Model polynomial box}

section
open Purelib.Polynomial
/-- Compute the differential-residual polynomial and cache its box norm bound. -/
@[expose] def build (model : Model polynomial box) : DifferentialResidualBounds model :=
  let value := (polynomial * Dense.Derivative.derivative model.value).scale 2 + Dense.Derivative.derivative polynomial *
    model.value
  ⟨value, fun point => by simp only [value, Dense.Basic.DensePolynomial.eval_add,
    Dense.Basic.DensePolynomial.eval_scale, Dense.Basic.DensePolynomial.eval_mul, differentialResidual]; ring1,
    Dense.Gaussian.Bounds.Box.denseEvalNormBound value box, rfl⟩

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
    normSq (differentialResidual polynomial (model.refine index).value point) ≤ Rational.Geometric.Basic.quarterRadius
      bounds.bound index := by
  induction index with
  | zero =>
      change normSq (differentialResidual polynomial model.value point) ≤ Rational.Geometric.Basic.quarterRadius
        bounds.bound 0
      rw [← bounds.value_eq, Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Rat.Fraction.Field.mul_one_direct, bounds.bound_eq]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound bounds.value inside
  | succ index previous =>
      change normSq (differentialResidual polynomial (model.refine index).step.value point) ≤ _
      apply ((Normalization.InverseModelDifferentialResidual.Model.step_differentialResidual_bound (model.refine index))
        inside).trans
      calc
        _ = normSq (differentialResidual polynomial (model.refine index).value point) * (1 / 4 : Coordinate) := by
          simp only [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul, -eq_self, -iff_self]
          rfl
        _ ≤ Rational.Geometric.Basic.quarterRadius bounds.bound index * (1 / 4 : Coordinate) :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct previous (by decide)
        _ = _ := by
          rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
            pow_succ]
          ring1

end DifferentialResidualBounds
end Purelib.Riemann.Normalization.InverseModelDifferentialResidual
