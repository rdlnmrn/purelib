module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Polynomial.Dense.Derivative
public import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Polynomial.Dense.Gaussian.Primitive.DerivativeBound
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Fixed primitive remainder budgets for all Newton indices

The numerator, its derivative, and the inverse-model derivative ceiling are
cached before choosing an index. The resulting remainder bound applies to
any checked primitive of the coefficient product, including generated data.
-/

namespace Purelib.Riemann.Normalization.InverseModelPrimitiveBounds

open Purelib.Riemann.Normalization.InverseModelDerivativeBounds
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance DensePrimitive)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative (derivative)

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached derivative bounds for the product of a fixed numerator and every refinement of an original inverse-root
model.

The record retains the numerator derivative and exact box majorants, combining them with the original root derivative
bounds in the product-rule estimate. -/
structure PrimitiveDerivativeBounds {polynomial : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    (root : DerivativeBounds clearance initial) (numerator : Polynomial) where
  /-- The retained derivative polynomial of the fixed original numerator. -/ numeratorDerivative : Polynomial
  /-- The retained polynomial agrees pointwise with the original numerator derivative. -/ numeratorDerivative_eq : ∀
    point, numeratorDerivative.eval point = (Dense.Derivative.derivative numerator).eval point
  /-- The cached squared-norm majorant of the original numerator on the box. -/ numeratorUpper : Coordinate
  /-- The numerator majorant equals the exact dense box evaluation bound. -/ numeratorUpper_eq : numeratorUpper =
    Bounds.Box.denseEvalNormBound numerator box
  /-- The cached squared-norm majorant of the retained numerator derivative. -/ derivativeUpper : Coordinate
  /-- The derivative majorant equals the exact dense box evaluation bound of the retained derivative polynomial. -/
    derivativeUpper_eq : derivativeUpper = Bounds.Box.denseEvalNormBound numeratorDerivative box
  /-- The cached product-rule squared-norm bound for all retained refinement coefficients. -/ bound : Coordinate
  /-- The bound is twice the sum of derivative-majorant times inverse-majorant and numerator-majorant times
    root-derivative bound. -/ bound_eq : bound = 2 * (derivativeUpper * root.inverseUpper + numeratorUpper * root.bound)

constructive_injectivity PrimitiveDerivativeBounds

namespace PrimitiveDerivativeBounds

variable {polynomial numerator : Polynomial} {box : Box} {clearance : RegionClearance polynomial box}
  {initial : Model polynomial box} {root : DerivativeBounds clearance initial}

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cache the numerator derivative, its box majorant and the product-rule bound from the original root derivative
bounds. -/
def build (root : DerivativeBounds clearance initial) (numerator : Polynomial) : PrimitiveDerivativeBounds root
  numerator :=
  let numeratorDerivative := Dense.Derivative.derivative numerator
  let numeratorUpper := Bounds.Box.denseEvalNormBound numerator box
  let derivativeUpper := Bounds.Box.denseEvalNormBound numeratorDerivative box
  ⟨numeratorDerivative, fun _ => rfl, numeratorUpper, rfl, derivativeUpper, rfl,
    2 * (derivativeUpper * root.inverseUpper + numeratorUpper * root.bound), rfl⟩

section
open Purelib.Polynomial.Dense.Gaussian
/-- The retained numerator squared-norm majorant is nonnegative. -/
theorem numeratorUpper_nonnegative (bounds : PrimitiveDerivativeBounds root numerator) : 0 ≤ bounds.numeratorUpper := by
  rw [bounds.numeratorUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The retained numerator derivative squared-norm majorant is nonnegative. -/
theorem derivativeUpper_nonnegative (bounds : PrimitiveDerivativeBounds root numerator) : 0 ≤ bounds.derivativeUpper :=
  by
  rw [bounds.derivativeUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

end

open Purelib.Data.Rat in
/-- The retained product-rule derivative bound is nonnegative. -/
theorem bound_nonnegative (bounds : PrimitiveDerivativeBounds root numerator) : 0 ≤ bounds.bound := by
  rw [bounds.bound_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.derivativeUpper_nonnegative root.inverseUpper_positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative root.bound_nonnegative))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Any polynomial with the exact numerator-times-refined-model evaluation equation satisfies the retained derivative
bound throughout the original box.

The polynomial identity preserves the original refinement index and numerator; the product-rule estimate uses the cached
numerator and root derivative majorants. -/
theorem coefficient_derivative_le (bounds : PrimitiveDerivativeBounds root numerator) (index : Nat)
    (coefficient : Polynomial)
    (equal : ∀ point, coefficient.eval point = numerator.eval point * (initial.refine index).value.eval point)
    {point : Gaussian} (inside : box.Contains point) :
    normSq ((Dense.Derivative.derivative coefficient).eval point) ≤ bounds.bound := by
  have same : (coefficient - numerator * (initial.refine index).value).isZero = true := by
    apply NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro sample _
    rw [equal, Dense.Basic.DensePolynomial.eval_mul]
  rw [Dense.Derivative.eval_derivative_eq_of_sub_isZero same point, Dense.Derivative.eval_derivative_mul]
  have numeratorLe : normSq (numerator.eval point) ≤ bounds.numeratorUpper :=
    by simpa only [Norm.Basic.normSq_eq_canonical] using (Bounds.Box.normSq_eval_le_denseEvalNormBound numerator
      inside).trans_eq bounds.numeratorUpper_eq.symm
  have derivativeLe : normSq ((Dense.Derivative.derivative numerator).eval point) ≤ bounds.derivativeUpper := by
    rw [← bounds.numeratorDerivative_eq]
    simpa only [Norm.Basic.normSq_eq_canonical] using (Bounds.Box.normSq_eval_le_denseEvalNormBound
      bounds.numeratorDerivative inside).trans_eq bounds.derivativeUpper_eq.symm
  rw [bounds.bound_eq]
  exact (show Basic.Canonical.normSq (((Dense.Derivative.derivative numerator).eval point * (initial.refine
    index).value.eval point) + (numerator.eval point * (Dense.Derivative.derivative (initial.refine index).value).eval
    point)) ≤ 2 * (Basic.Canonical.normSq ((Dense.Derivative.derivative numerator).eval point * (initial.refine
    index).value.eval point) + Basic.Canonical.normSq (numerator.eval point * (Dense.Derivative.derivative
    (initial.refine index).value).eval point)) from by
    simpa only [Norm.Basic.normSq_eq_canonical] using
      Norm.Bounds.normSq_add_le_two ((Dense.Derivative.derivative numerator).eval point * (initial.refine
        index).value.eval point) (numerator.eval point * (Dense.Derivative.derivative (initial.refine index).value).eval
        point)).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add
    (by
      rw [Basic.Canonical.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct derivativeLe (root.value_le _ inside)
        (Basic.Canonical.normSq_nonneg _) bounds.derivativeUpper_nonnegative)
    (by
      rw [Basic.Canonical.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct numeratorLe (root.refine_derivative_le index inside)
        (Basic.Canonical.normSq_nonneg _) bounds.numeratorUpper_nonnegative)) (by decide))

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Bound the primitive increment's error from its original coefficient's linear increment between two points of the
retained box.

The coefficient is exactly the fixed numerator times the indexed original inverse-root refinement. The squared error is
bounded by four times the retained derivative bound times the fourth power of the endpoint distance. -/
theorem primitive_increment_le (bounds : PrimitiveDerivativeBounds root numerator) (index : Nat)
    {coefficient : Polynomial} (primitive : DensePrimitive coefficient box)
    (equal : ∀ point, coefficient.eval point = numerator.eval point * (initial.refine index).value.eval point)
    {start finish : Gaussian} (startInside : box.Contains start) (finishInside : box.Contains finish) :
    normSq (primitive.value.eval finish - primitive.value.eval start - coefficient.eval start * (finish - start)) ≤
      4 * bounds.bound * normSq (finish - start) ^ 2 :=
  by
  have bounded : ∀ point, box.Contains point →
      Data.Gaussian.Norm.Basic.normSq ((Dense.Derivative.derivative coefficient).eval point) ≤ bounds.bound := fun point
        inside => by
    rw [Norm.Basic.normSq_eq_canonical]
    exact bounds.coefficient_derivative_le index coefficient equal inside
  have estimate := primitive.increment_bound_of_derivative startInside finishInside bounds.bound
    bounds.bound_nonnegative bounded
  simpa only [Norm.Basic.normSq_eq_canonical] using estimate

end PrimitiveDerivativeBounds

end Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
