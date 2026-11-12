module

public import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
public import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Decaying differential mismatches of inverse-root primitive models

The same original Newton model supplies its square and differential
residuals. A fixed polynomial numerator and positive sheet exponent retain
one cleared coefficient and one rational decay budget. The budget controls
the actual derivative of the polynomial primitive at every finite stage.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelPrimitiveResidual

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat.Rounding

/-- The exact differential mismatch between one finite polynomial primitive and its algebraic differential model. -/
@[expose] def primitiveMismatch {polynomial : Polynomial} {box : Box} (model : Model polynomial box)
    (numerator coefficient : Polynomial) (index : Nat) (point : Gaussian) : Gaussian :=
  (Derivative.derivative (numerator * Power.power model.value (index + 1))).eval point -
    half * coefficient.eval point * model.value.eval point ^ (index + 3)

/-- The rational decay scale assembled from retained primitive, inverse-model and residual majorants. -/
@[expose] def decayScale {polynomial numerator : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    (root : DerivativeBounds clearance initial) (residual : DifferentialResidualBounds initial)
    (primitive : PrimitiveDerivativeBounds root numerator) (coefficientUpper inversePower factorNorm : Coordinate) :
    Coordinate :=
  (coefficientUpper * inversePower * root.inverseUpper * initial.bound +
    factorNorm * primitive.numeratorUpper * inversePower * residual.bound) / (2 * clearance.bound)

set_option genInjectivity false in
/-- Retain the cleared odd-primitive coefficient and its actual finite Newton mismatch budget.

The three indexed source caches retain the same initial model, polynomial,
box and numerator. The power and exponent factor are computed once and used
by the coefficient and the decay scale rather than repeated downstream.
-/
structure PrimitiveResidualBounds {polynomial numerator : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    (root : DerivativeBounds clearance initial) (residual : DifferentialResidualBounds initial)
    (primitive : PrimitiveDerivativeBounds root numerator) (index : Nat) where
  /-- The cached positive-exponent scalar coefficient. -/
  factor : Gaussian
  /-- The factor is exactly the original exponent index plus one. -/
  factor_eq : factor = (index : Gaussian) + 1
  /-- The cached quadrance of the same exponent factor. -/
  factorNorm : Coordinate
  /-- The quadrance was computed from the retained factor. -/
  factorNorm_eq : factorNorm = normSq factor
  /-- The cleared derivative numerator using the original retained derivative caches. -/
  coefficient : Polynomial
  /-- The coefficient has the original algebraic primitive differential readback. -/
  coefficient_eq : ∀ point, coefficient.eval point =
    2 * polynomial.eval point * (Derivative.derivative numerator).eval point -
      factor * numerator.eval point * (Derivative.derivative polynomial).eval point
  /-- The cached squared-norm ceiling of the retained coefficient on the original box. -/
  coefficientUpper : Coordinate
  /-- The ceiling is computed on the original coefficient and box. -/
  coefficientUpper_eq : coefficientUpper = Bounds.Box.denseEvalNormBound coefficient box
  /-- The retained exponent power of the original inverse-model norm ceiling. -/
  inversePower : Coordinate
  /-- The power uses the same original inverse-model norm ceiling and exponent index. -/
  inversePower_eq : inversePower = root.inverseUpper ^ index
  /-- The cached rational scale of the finite quarter-radius mismatch bound. -/
  scale : Coordinate
  /-- The scale consumes the same retained powers, factors and coefficient ceilings. -/
  scale_eq : scale = decayScale root residual primitive coefficientUpper inversePower factorNorm

constructive_injectivity PrimitiveResidualBounds

namespace PrimitiveResidualBounds

variable {polynomial numerator : Polynomial} {box : Box} {clearance : RegionClearance polynomial box}
  {initial : Model polynomial box} {root : DerivativeBounds clearance initial}
  {residual : DifferentialResidualBounds initial} {primitive : PrimitiveDerivativeBounds root numerator}
  {index : Nat}

/-- Construct the complete primitive mismatch budget from the original retained derivative and residual caches. -/
@[expose] def build (root : DerivativeBounds clearance initial) (residual : DifferentialResidualBounds initial)
    (primitive : PrimitiveDerivativeBounds root numerator) (index : Nat) :
    PrimitiveResidualBounds root residual primitive index :=
  let factor := (index : Gaussian) + 1
  let factorNorm := normSq factor
  let coefficient := (polynomial * primitive.numeratorDerivative).scale 2 -
    (numerator * root.polynomialDerivative).scale factor
  let coefficientUpper := Bounds.Box.denseEvalNormBound coefficient box
  let inversePower := root.inverseUpper ^ index
  ⟨factor, rfl, factorNorm, rfl, coefficient, fun point => by
    rewrite [eval_sub, eval_scale, eval_mul, eval_scale, eval_mul,
      primitive.numeratorDerivative_eq point, root.polynomialDerivative_eq point]
    ring1, coefficientUpper, rfl, inversePower, rfl,
    decayScale root residual primitive coefficientUpper inversePower factorNorm, rfl⟩

/-- The retained cleared coefficient ceiling is nonnegative. -/
theorem coefficientUpper_nonnegative (bounds : PrimitiveResidualBounds root residual primitive index) :
    0 ≤ bounds.coefficientUpper := by
  rewrite [bounds.coefficientUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The retained exponent-factor quadrance is nonnegative. -/
theorem factorNorm_nonnegative (bounds : PrimitiveResidualBounds root residual primitive index) :
    0 ≤ bounds.factorNorm := by
  rewrite [bounds.factorNorm_eq]
  exact normSq_nonneg _

/-- The retained inverse-model norm power is nonnegative. -/
theorem inversePower_nonnegative (bounds : PrimitiveResidualBounds root residual primitive index) :
    0 ≤ bounds.inversePower := by
  rewrite [bounds.inversePower_eq]
  exact Arithmetic.pow_nonneg_direct root.inverseUpper_positive.le index

/-- The complete retained quarter-radius mismatch scale is nonnegative. -/
theorem scale_nonnegative (bounds : PrimitiveResidualBounds root residual primitive index) : 0 ≤ bounds.scale := by
  rewrite [bounds.scale_eq, decayScale]
  apply Fraction.Order.Field.div_nonneg_direct
  · apply add_nonneg
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct bounds.coefficientUpper_nonnegative
            bounds.inversePower_nonnegative) root.inverseUpper_positive.le) initial.bound_nonnegative
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct bounds.factorNorm_nonnegative
            primitive.numeratorUpper_nonnegative) bounds.inversePower_nonnegative) residual.bound_nonnegative
  · exact Arithmetic.mul_nonneg_direct (by decide) clearance.positive.le

/-- Every refined inverse-root primitive mismatch obeys the cached geometric quarter-radius budget.

The point remains in the original cleared box. The bound charges both the
actual square residual and actual differential residual of that same
finite refinement, with no exact-root assertion for its polynomial value.
-/
theorem refine_bound (bounds : PrimitiveResidualBounds root residual primitive index) (stage : Nat)
    {point : Gaussian} (inside : box.Contains point) :
    normSq (primitiveMismatch (initial.refine stage) numerator bounds.coefficient index point) ≤
      quarterRadius bounds.scale stage := by
  let model := initial.refine stage
  let mismatch := primitiveMismatch model numerator bounds.coefficient index point
  have coefficientLe : normSq (bounds.coefficient.eval point) ≤ bounds.coefficientUpper := by
    have bound := Bounds.Box.normSq_eval_le_denseEvalNormBound bounds.coefficient inside
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans_eq bounds.coefficientUpper_eq.symm
  have numeratorLe : normSq (numerator.eval point) ≤ primitive.numeratorUpper := by
    have bound := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans_eq primitive.numeratorUpper_eq.symm
  have powerLe : normSq (model.value.eval point) ^ index ≤ bounds.inversePower := by
    rewrite [bounds.inversePower_eq]
    exact Arithmetic.pow_le_pow_direct (normSq_nonneg _) (root.value_le model inside) index
  have nextPowerLe : normSq (model.value.eval point) ^ (index + 1) ≤
      bounds.inversePower * root.inverseUpper := by
    rewrite [pow_succ]
    exact Arithmetic.mul_le_mul_direct powerLe (root.value_le model inside)
      (normSq_nonneg _) bounds.inversePower_nonnegative
  have squareLe : normSq (model.residual.eval point) ≤ quarterRadius initial.bound stage := by
    have bound := initial.refine_residualBound stage point inside
    rewrite [← model.residual_eq] at bound
    exact bound
  have differentialLe : normSq (differentialResidual polynomial model.value point) ≤
      quarterRadius residual.bound stage := residual.refine_bound stage inside
  have powerNorm : normSq (model.value.eval point ^ index) = normSq (model.value.eval point) ^ index := by
    have equation := Power.normSq_pow (model.value.eval point) index
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at equation
    exact equation
  have nextPowerNorm : normSq (model.value.eval point ^ (index + 1)) =
      normSq (model.value.eval point) ^ (index + 1) := by
    have equation := Power.normSq_pow (model.value.eval point) (index + 1)
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at equation
    exact equation
  have firstLe : normSq (bounds.coefficient.eval point * model.value.eval point ^ (index + 1) *
      model.residual.eval point) ≤ bounds.coefficientUpper * bounds.inversePower * root.inverseUpper *
        quarterRadius initial.bound stage := by
    rewrite [normSq_mul, normSq_mul, nextPowerNorm]
    have initialProduct := Arithmetic.mul_le_mul_direct coefficientLe nextPowerLe
      (Arithmetic.pow_nonneg_direct (normSq_nonneg _) _) bounds.coefficientUpper_nonnegative
    have product := Arithmetic.mul_le_mul_direct initialProduct squareLe (normSq_nonneg _)
      (Arithmetic.mul_nonneg_direct bounds.coefficientUpper_nonnegative
        (Arithmetic.mul_nonneg_direct bounds.inversePower_nonnegative root.inverseUpper_positive.le))
    simpa only [Fraction.mul_assoc] using product
  have secondLe : normSq (bounds.factor * numerator.eval point * model.value.eval point ^ index *
      differentialResidual polynomial model.value point) ≤ bounds.factorNorm * primitive.numeratorUpper *
        bounds.inversePower * quarterRadius residual.bound stage := by
    rewrite [normSq_mul, normSq_mul, normSq_mul, powerNorm, ← bounds.factorNorm_eq]
    have initialProduct := Arithmetic.mul_le_mul_of_nonneg_left_direct numeratorLe
      bounds.factorNorm_nonnegative
    have powerProduct := Arithmetic.mul_le_mul_direct initialProduct powerLe
      (Arithmetic.pow_nonneg_direct (normSq_nonneg _) _) (Arithmetic.mul_nonneg_direct
        bounds.factorNorm_nonnegative primitive.numeratorUpper_nonnegative)
    exact Arithmetic.mul_le_mul_direct powerProduct differentialLe (normSq_nonneg _)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct bounds.factorNorm_nonnegative primitive.numeratorUpper_nonnegative)
        bounds.inversePower_nonnegative)
  have identity : 2 * polynomial.eval point * mismatch =
      bounds.coefficient.eval point * model.value.eval point ^ (index + 1) * model.residual.eval point +
        bounds.factor * numerator.eval point * model.value.eval point ^ index *
          differentialResidual polynomial model.value point := by
    have equation := InverseModelDifferentialResidual.Model.primitive_differentialResidual model numerator index point
    dsimp only [mismatch, primitiveMismatch]
    rewrite [bounds.coefficient_eq, bounds.factor_eq]
    exact equation
  have cleared : 4 * normSq (polynomial.eval point) * normSq mismatch ≤
      2 * (bounds.coefficientUpper * bounds.inversePower * root.inverseUpper * quarterRadius initial.bound stage +
        bounds.factorNorm * primitive.numeratorUpper * bounds.inversePower * quarterRadius residual.bound stage) := by
    have scalar := Norm.Bounds.normSq_add_le_two
      (bounds.coefficient.eval point * model.value.eval point ^ (index + 1) * model.residual.eval point)
      (bounds.factor * numerator.eval point * model.value.eval point ^ index *
        differentialResidual polynomial model.value point)
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
      Norm.Basic.normSq_eq_canonical, ← identity, normSq_mul, normSq_mul,
      show normSq (2 : Gaussian) = 4 by decide] at scalar
    exact scalar.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstLe secondLe)
      (by decide))
  have lower : 4 * clearance.bound * normSq mismatch ≤ 4 * normSq (polynomial.eval point) * normSq mismatch :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by simpa only [Norm.Basic.normSq_eq_canonical] using clearance.lower point inside) (by decide))
      (normSq_nonneg _)
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4 * clearance.bound) _
    (Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4) clearance.positive)
  have scaled := lower.trans cleared
  change normSq mismatch * (4 * clearance.bound) ≤ _
  rewrite [mul_comm (normSq mismatch)]
  have budget : 2 *
      (bounds.coefficientUpper * bounds.inversePower * root.inverseUpper * quarterRadius initial.bound stage +
        bounds.factorNorm * primitive.numeratorUpper * bounds.inversePower * quarterRadius residual.bound stage) =
      quarterRadius bounds.scale stage * (4 * clearance.bound) := by
    rewrite [bounds.scale_eq, decayScale, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow,
      quarterRadius_eq_mul_pow]
    have cancelled := Fraction.Field.div_mul_cancel_of_ne
      (bounds.coefficientUpper * bounds.inversePower * root.inverseUpper * initial.bound +
        bounds.factorNorm * primitive.numeratorUpper * bounds.inversePower * residual.bound)
      (2 * clearance.bound) (Arithmetic.mul_pos_direct
        (by decide : (0 : Coordinate) < 2) clearance.positive).ne'
    calc
      _ = 2 *
        ((bounds.coefficientUpper * bounds.inversePower * root.inverseUpper * initial.bound +
          bounds.factorNorm * primitive.numeratorUpper * bounds.inversePower * residual.bound) /
            (2 * clearance.bound) * (2 * clearance.bound)) * (1 / 4 : Coordinate) ^ stage := by
        rewrite [cancelled]
        ring1
      _ = _ := by ring1
  exact scaled.trans_eq budget

/-- The original finite primitive coefficient readback at one retained refinement stage. -/
@[expose] def PrimitiveReadback (stage : Nat) (source : Polynomial) : Prop :=
  ∀ point, source.eval point = numerator.eval point * (initial.refine stage).value.eval point ^ (index + 1)

/-- The original finite algebraic differential coefficient readback at the same retained stage. -/
@[expose] def DifferentialReadback (bounds : PrimitiveResidualBounds root residual primitive index)
    (stage : Nat) (source : Polynomial) : Prop :=
  ∀ point, source.eval point =
    half * bounds.coefficient.eval point * (initial.refine stage).value.eval point ^ (index + 3)

/-- Transfer the source-derived mismatch budget to the two actual retained coefficient polynomials.

The readbacks come from the original finite coefficient constructors. A finite
zero-coefficient check identifies the primitive's automatic derivative,
without rebuilding its table or evaluating an independent root channel. -/
theorem cached_refine_bound (bounds : PrimitiveResidualBounds root residual primitive index) (stage : Nat)
    (primitiveSource differentialSource : Polynomial)
    (primitiveReadback : PrimitiveReadback (numerator := numerator) (initial := initial) (index := index)
      stage primitiveSource)
    (differentialReadback : bounds.DifferentialReadback stage differentialSource)
    {point : Gaussian} (inside : box.Contains point) :
    normSq ((Derivative.derivative primitiveSource).eval point - differentialSource.eval point) ≤
      quarterRadius bounds.scale stage := by
  have identical : (primitiveSource - numerator * Power.power (initial.refine stage).value (index + 1)).isZero =
      true := by
    apply Extensionality.isZero_of_eval_eq_zero
    intro sample
    rewrite [eval_sub, primitiveReadback sample, eval_mul, Power.eval_power]
    exact sub_self _
  rewrite [Derivative.eval_derivative_eq_of_sub_isZero identical point, differentialReadback point]
  exact bounds.refine_bound stage inside

/-- Choose a certified finite stage paying a request from the retained original primitive source budget. -/
@[expose] def choose (bounds : PrimitiveResidualBounds root residual primitive index) (current : Nat)
    (target : Coordinate) (targetPositive : 0 < target) : Search.Selection bounds.scale current target :=
  Search.Selection.build bounds.scale bounds.scale_nonnegative current target targetPositive

/-- The same original finite primitive model meets the allowance retained by its actual successful selection. -/
theorem selected_bound (bounds : PrimitiveResidualBounds root residual primitive index) {current : Nat}
    {target : Coordinate} (selection : Search.Selection bounds.scale current target) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (primitiveMismatch (initial.refine selection.stage) numerator bounds.coefficient index point) ≤
      selection.allowance := by
  rewrite [selection.allowance_eq]
  exact bounds.refine_bound selection.stage inside

/-- The retained finite primitive model strictly meets the original request at its selected stage. -/
theorem selected_accurate_bound (bounds : PrimitiveResidualBounds root residual primitive index) {current : Nat}
    {target : Coordinate} (selection : Search.Selection bounds.scale current target) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (primitiveMismatch (initial.refine selection.stage) numerator bounds.coefficient index point) < target :=
  (bounds.selected_bound selection inside).trans_lt selection.accurate

/-- The actual retained source polynomial coefficients meet the allowance chosen for their original Newton source. -/
theorem selected_cached_bound (bounds : PrimitiveResidualBounds root residual primitive index) {current : Nat}
    {target : Coordinate} (selection : Search.Selection bounds.scale current target)
    (primitiveSource differentialSource : Polynomial)
    (primitiveReadback : PrimitiveReadback (numerator := numerator) (initial := initial) (index := index)
      selection.stage primitiveSource)
    (differentialReadback : bounds.DifferentialReadback selection.stage differentialSource)
    {point : Gaussian} (inside : box.Contains point) :
    normSq ((Derivative.derivative primitiveSource).eval point - differentialSource.eval point) ≤
      selection.allowance := by
  rewrite [selection.allowance_eq]
  exact bounds.cached_refine_bound selection.stage primitiveSource differentialSource
    primitiveReadback differentialReadback inside

/-- The actual retained source coefficients strictly pay the original request at the selected finite stage. -/
theorem selected_cached_accurate_bound (bounds : PrimitiveResidualBounds root residual primitive index) {current : Nat}
    {target : Coordinate} (selection : Search.Selection bounds.scale current target)
    (primitiveSource differentialSource : Polynomial)
    (primitiveReadback : PrimitiveReadback (numerator := numerator) (initial := initial) (index := index)
      selection.stage primitiveSource)
    (differentialReadback : bounds.DifferentialReadback selection.stage differentialSource)
    {point : Gaussian} (inside : box.Contains point) :
    normSq ((Derivative.derivative primitiveSource).eval point - differentialSource.eval point) < target :=
  (bounds.selected_cached_bound selection primitiveSource differentialSource
    primitiveReadback differentialReadback inside).trans_lt selection.accurate

end PrimitiveResidualBounds

end Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
