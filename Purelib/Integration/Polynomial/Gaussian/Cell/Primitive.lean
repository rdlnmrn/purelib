module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Geometry.Rational.Affine
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Composition
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Polynomial primitive comparisons for an original integration cell

The local primitive and derivative residual are retained finite coefficient
tables. A coefficient-computed ceiling bounds the difference between the
primitive increment and the original cell's actual polynomial integral.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Primitive

open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Dense.Gaussian.Basic
open Dense.Gaussian.Primitive.Certificate (DensePrimitive)

/-- The closed unit parameter interval used by an integration cell. -/
@[expose] def unitInterval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩

/-- A rational box containing the original real unit parameter interval. -/
@[expose] def unitBox : Box := ⟨0, 1, 0, 0, by decide, by decide⟩

/-- The unit affine line embeds a bounded rational parameter in the unit box. -/
theorem unitLine_inside {parameter : Fraction.Rational}
    (inside : unitInterval.Contains parameter) :
    unitBox.Contains (Affine.line 0 1 parameter) := by
  change unitBox.Contains (0 + Data.Gaussian.Cast.Path.ofCoordinate parameter * 1)
  rw [Basic.mul_one, Basic.zero_add]
  exact ⟨inside.1, inside.2, le_rfl, le_rfl⟩

/-- The local integrand after multiplying by the original geometric displacement. -/
@[expose] def displacedPolynomial (cell : Basic.CellModel) :
    CanonicalCoefficients.CoefficientPolynomial :=
  toDense
    (Ascending.Gaussian.Arithmetic.scale cell.displacement cell.polynomial)

/-- Its exact dense primitive reads the original cell's integral as its unit increment. -/
theorem displacedPrimitive_increment (cell : Basic.CellModel) :
    (DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox).value.eval 1 -
      (DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox).value.eval 0 =
        cell.integralSample := by
  let scaled := Ascending.Gaussian.Arithmetic.scale cell.displacement cell.polynomial
  have reverseTable :
      (⟨(displacedPolynomial cell).coeffs.reverse⟩ :
        Ascending.Gaussian.CoefficientPolynomial) = scaled := by
    change (⟨scaled.coefficients.reverse.reverse⟩ : Ascending.Gaussian.CoefficientPolynomial) = scaled
    rw [Purelib.Data.List.Reverse.reverse_reverse]
  change (Dense.Gaussian.Antiderivative.denseAntiderivative (displacedPolynomial cell)).eval 1 -
    (Dense.Gaussian.Antiderivative.denseAntiderivative (displacedPolynomial cell)).eval 0 = _
  rw [Dense.Gaussian.Antiderivative.denseAntiderivative, reverseTable,
    toDense_eval,
    toDense_eval]
  exact Ascending.Gaussian.Integral.definiteIntegral_scale cell.displacement cell.polynomial 0 1

/-- The spatial coordinate of the original cell as an exact local-parameter polynomial. -/
@[expose] def coordinate (cell : Basic.CellModel) :
    CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[cell.displacement, cell.start]⟩

/-- The retained cell coordinate polynomial evaluates along the original affine segment. -/
theorem coordinate_eval (cell : Basic.CellModel) (parameter : Basic.Canonical) :
    (coordinate cell).eval parameter = cell.start + parameter * cell.displacement := by
  change (0 * parameter + cell.displacement) * parameter + cell.start = _
  ring1

/-- The derivative of the original local coordinate is its exact retained geometric displacement. -/
theorem coordinate_derivative_eval (cell : Basic.CellModel) (parameter : Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative (coordinate cell)).eval parameter = cell.displacement := by
  rw [Dense.Gaussian.GCD.derivative, Dense.Derivative.eval_derivative]
  change (0 * parameter + 0) * parameter + (0 * parameter + cell.displacement) = cell.displacement
  ring1

/-- Compile a spatial primitive into the original cell's local parameter. -/
@[expose] def spatialPrimitive (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) :
    CanonicalCoefficients.CoefficientPolynomial :=
  Dense.Gaussian.Substitution.Composition.compose value (coordinate cell)

/-- A compiled spatial primitive starts at the original spatial starting value. -/
theorem spatialPrimitive_start (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) :
    (spatialPrimitive cell value).eval 0 = value.eval cell.start := by
  rw [spatialPrimitive, Dense.Gaussian.Substitution.Composition.eval_compose, coordinate_eval,
    Basic.zero_mul, Basic.add_zero]

/-- A compiled spatial primitive finishes at the original spatial finishing value. -/
theorem spatialPrimitive_finish (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) :
    (spatialPrimitive cell value).eval 1 = value.eval cell.finish := by
  rw [spatialPrimitive, Dense.Gaussian.Substitution.Composition.eval_compose, coordinate_eval, Basic.one_mul]
  have endpoint : cell.start + cell.displacement = cell.finish := by
    unfold Basic.CellModel.displacement
    ring1
  rw [endpoint]

/-- The original local primitive derivative minus the same displaced integrand. -/
@[expose] def residualPolynomial (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) :
    CanonicalCoefficients.CoefficientPolynomial :=
  Dense.Gaussian.GCD.derivative value - displacedPolynomial cell

/-- A bound on the retained local derivative residual at each original rational unit parameter. -/
@[expose] def ResidualBound (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) (bound : Fraction.Rational) : Prop :=
  ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
    Norm.Basic.normSq ((residualPolynomial cell value).eval (Affine.line 0 1 parameter)) ≤ bound

/-- Spatial compilation reads its derivative residual at the original coordinate and original cell polynomial.

The same geometric displacement supplies the Jacobian once. This is a
scalar readback of the retained finite coefficient calculation. -/
theorem spatial_residual_readback (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) (parameter : Fraction.Rational) :
    (residualPolynomial cell (spatialPrimitive cell value)).eval (Affine.line 0 1 parameter) =
      cell.displacement *
        ((Dense.Gaussian.GCD.derivative value).eval (Affine.line cell.start cell.displacement parameter) -
          Gaussian.Evaluation.eval cell.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter)) := by
  rw [residualPolynomial, Dense.Basic.DensePolynomial.eval_sub, spatialPrimitive,
    Dense.Gaussian.GCD.derivative, Dense.Gaussian.Substitution.Composition.derivative_compose]
  have slope := coordinate_derivative_eval cell (Affine.line 0 1 parameter)
  change (Dense.Derivative.derivative (coordinate cell)).eval (Affine.line 0 1 parameter) = cell.displacement at slope
  rw [slope, coordinate_eval]
  have unitParameter : Affine.line (0 : Basic.Canonical) 1 parameter =
      Data.Gaussian.Cast.Path.ofCoordinate parameter := by
    change (0 : Basic.Canonical) + Data.Gaussian.Cast.Path.ofCoordinate parameter * 1 = _
    rw [Basic.mul_one, Basic.zero_add]
  rw [unitParameter, displacedPolynomial, toDense_eval,
    Gaussian.Evaluation.eval_scale]
  change _ = cell.displacement *
    ((Dense.Gaussian.GCD.derivative value).eval (cell.start +
      Data.Gaussian.Cast.Path.ofCoordinate parameter * cell.displacement) - _)
  rw [Dense.Gaussian.GCD.derivative]
  ring1

set_option genInjectivity false in
/-- A local polynomial primitive with a cached derivative, displacement residual and checked norm ceiling.

The original cell determines the integrand and displacement. The residual
compares the retained primitive derivative with precisely that integrand;
its ceiling bounds that same residual on the original unit interval. -/
structure Comparison (cell : Basic.CellModel) where
  /-- The retained local-parameter primitive polynomial. -/
  value : CanonicalCoefficients.CoefficientPolynomial
  /-- The retained derivative of that exact primitive. -/
  derivative : CanonicalCoefficients.CoefficientPolynomial
  /-- The derivative cache is the finite derivative of the retained value. -/
  derivative_eq : derivative = Dense.Gaussian.GCD.derivative value
  /-- The retained derivative minus the original displaced integrand. -/
  residual : CanonicalCoefficients.CoefficientPolynomial
  /-- The residual cache uses that same derivative and original integrand. -/
  residual_eq : residual = derivative - displacedPolynomial cell
  /-- The retained ceiling of the derivative residual quadrance. -/
  bound : Fraction.Rational
  /-- Every original unit-interval residual reading obeys the retained ceiling. -/
  residualBound : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
    Norm.Basic.normSq (residual.eval (Affine.line 0 1 parameter)) ≤ bound

constructive_injectivity Comparison

namespace Comparison

/-- Construct local primitive comparison data from a proved derivative residual ceiling.

The derivative and residual are computed and cached once. The bound is a
coefficient-level quantitative obligation, rather than an integral or
endpoint-difference conclusion. -/
@[expose] def ofBound (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial)
    (bound : Fraction.Rational) (uniform : ResidualBound cell value bound) : Comparison cell :=
  let derivative := Dense.Gaussian.GCD.derivative value
  let residual := derivative - displacedPolynomial cell
  ⟨value, derivative, rfl, residual, rfl, bound, uniform⟩

/-- Cache all finite derivative and residual calculations for the supplied local primitive. -/
@[expose] def build (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) : Comparison cell :=
  let derivative := Dense.Gaussian.GCD.derivative value
  let residual := derivative - displacedPolynomial cell
  let bound := Dense.Gaussian.Bounds.Box.denseEvalNormBound residual unitBox
  ⟨value, derivative, rfl, residual, rfl, bound,
    fun _ inside => Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound residual
      (unitLine_inside inside)⟩

/-- Compile and cache the original spatial primitive using the coefficient-computed local residual ceiling. -/
@[expose] def ofSpatial (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial) : Comparison cell :=
  build cell (spatialPrimitive cell value)

/-- Compile the original spatial primitive using its retained source-derived residual ceiling.

The original derivative, coefficient readings and geometric displacement
determine the uniform obligation. Compilation constructs the local
primitive and its actual derivative residual without recomputing a separate
Horner ceiling. -/
@[expose] def ofSpatialBound (cell : Basic.CellModel)
    (value : CanonicalCoefficients.CoefficientPolynomial)
    (bound : Fraction.Rational)
    (uniform : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
      Norm.Basic.normSq
        (cell.displacement *
          ((Dense.Gaussian.GCD.derivative value).eval (Affine.line cell.start cell.displacement parameter) -
            Gaussian.Evaluation.eval cell.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter))) ≤
        bound) : Comparison cell :=
  ofBound cell (spatialPrimitive cell value) bound (by
    intro parameter inside
    rw [spatial_residual_readback]
    exact uniform parameter inside)

/-- Retain a source-derived ceiling while reusing the original primitive and derivative residual caches.

The supplied bound concerns the retained residual at every original unit
parameter. It can be derived from refinement residuals and chart clearance;
no primitive-integral comparison is required. -/
@[expose] def withBound {cell : Basic.CellModel} (comparison : Comparison cell)
    (bound : Fraction.Rational)
    (residualBound : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
      Norm.Basic.normSq (comparison.residual.eval (Affine.line 0 1 parameter)) ≤ bound) : Comparison cell :=
  { comparison with bound := bound, residualBound := residualBound }

/-- The retained derivative residual ceiling is nonnegative. -/
theorem bound_nonnegative {cell : Basic.CellModel} (comparison : Comparison cell) :
    0 ≤ comparison.bound :=
  (Norm.Basic.normSq_nonneg _).trans
    (comparison.residualBound 0 ⟨le_rfl, by decide⟩)

/-- Every bounded rational parameter obeys the retained derivative residual ceiling. -/
theorem derivative_error_le {cell : Basic.CellModel} (comparison : Comparison cell)
    {parameter : Fraction.Rational} (inside : unitInterval.Contains parameter) :
    Norm.Basic.normSq
        ((Dense.Gaussian.GCD.derivative comparison.value).eval (Affine.line 0 1 parameter) -
          (displacedPolynomial cell).eval (Affine.line 0 1 parameter)) ≤ comparison.bound := by
  have bound := comparison.residualBound parameter inside
  rw [comparison.residual_eq, Dense.Basic.DensePolynomial.eval_sub,
    comparison.derivative_eq] at bound
  exact bound

/-- The original polynomial cell's integral differs from the retained primitive increment by at most twice its ceiling.

Finite midpoint refinement removes the polynomial Taylor remainder. The
result refers to the original integral sample and retains the same local
primitive and cached derivative residual throughout. -/
theorem integral_error_le {cell : Basic.CellModel} (comparison : Comparison cell) :
    Norm.Basic.normSq
        (comparison.value.eval 1 - comparison.value.eval 0 - cell.integralSample) ≤
      2 * comparison.bound := by
  let left := Dense.Gaussian.Primitive.Certificate.derivativePrimitive comparison.value unitBox
  let right := DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox
  have estimate := Dense.Gaussian.Primitive.Segment.Comparison.DensePrimitive.difference_increment_le
    left right 1 0 1 (by decide) unitInterval
    (fun _ inside => unitLine_inside inside) (fun _ inside => unitLine_inside inside)
    comparison.bound
    (by
      intro parameter inside
      rw [Basic.one_mul]
      exact comparison.derivative_error_le inside)
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have unitOne : Affine.line (0 : Basic.Canonical) 1 1 = 1 := by
    change (0 : Basic.Canonical) + 1 * 1 = 1
    ring1
  rw [unitOne, Affine.line_zero, Basic.one_mul,
    show Norm.Basic.normSq (1 : Basic.Canonical) = 1 by decide,
    show (1 - 0 : Fraction.Rational) ^ 2 = 1 by decide,
    Fraction.Field.mul_one_direct, Fraction.Field.mul_one_direct,
    displacedPrimitive_increment] at estimate
  exact estimate

end Comparison

/-- A uniform displaced-integrand ceiling bounds the original polynomial cell's integral quadrance.

The comparison uses the zero primitive and the same original cell and
polynomial. Finite midpoint refinement controls their actual integral,
without an assumed analytic integral or a new sampling program.
-/
theorem integral_normSq_le (cell : Basic.CellModel) (bound : Fraction.Rational)
    (uniform : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
      Norm.Basic.normSq (cell.displacement *
        Gaussian.Evaluation.eval cell.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter)) ≤
          bound) : Norm.Basic.normSq cell.integralSample ≤ 2 * bound := by
  let comparison := Comparison.ofSpatialBound cell (0 : CanonicalCoefficients.CoefficientPolynomial) bound (by
    intro parameter inside
    have zeroDerivative :
        (Dense.Gaussian.GCD.derivative (0 : CanonicalCoefficients.CoefficientPolynomial)).eval
          (Affine.line cell.start cell.displacement parameter) = 0 := rfl
    rw [zeroDerivative]
    have negative : cell.displacement *
        (0 - Gaussian.Evaluation.eval cell.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter)) =
        -(cell.displacement * Gaussian.Evaluation.eval cell.polynomial
          (Data.Gaussian.Cast.Path.ofCoordinate parameter)) := by ring1
    rw [negative, Norm.Basic.normSq_neg]
    exact uniform parameter inside)
  have estimate := comparison.integral_error_le
  change Norm.Basic.normSq
    ((spatialPrimitive cell (0 : CanonicalCoefficients.CoefficientPolynomial)).eval 1 -
      (spatialPrimitive cell (0 : CanonicalCoefficients.CoefficientPolynomial)).eval 0 - cell.integralSample) ≤ _
        at estimate
  rw [spatialPrimitive_finish, spatialPrimitive_start,
    Dense.Basic.DensePolynomial.eval_zero, Dense.Basic.DensePolynomial.eval_zero,
    Basic.sub_self, Basic.zero_sub, Norm.Basic.normSq_neg] at estimate
  exact estimate

/-- Equal original cell endpoints and a uniform polynomial difference bound control their actual integral samples.

The two finite coefficient tables remain independent. Their exact dense
primitives and the same original displacement reduce the estimate to the
existing whole-segment residual comparison, without a polynomial-degree
factor or a retained Taylor remainder floor.
-/
theorem integral_difference_le (first last : Basic.CellModel)
    (start_eq : first.start = last.start) (finish_eq : first.finish = last.finish)
    (bound : Fraction.Rational)
    (bounded : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
      Norm.Basic.normSq
        (Gaussian.Evaluation.eval first.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter) -
          Gaussian.Evaluation.eval last.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter)) ≤
        bound) :
    Norm.Basic.normSq (first.integralSample - last.integralSample) ≤
      2 * bound * Norm.Basic.normSq first.displacement := by
  let source := DensePrimitive.ofPolynomial (displacedPolynomial first) unitBox
  have displacement_eq : first.displacement = last.displacement := by
    change first.finish - first.start = last.finish - last.start
    rewrite [start_eq, finish_eq]
    rfl
  have residual : ResidualBound last source.value (Norm.Basic.normSq first.displacement * bound) := by
    intro parameter inside
    have unitParameter : Affine.line (0 : Basic.Canonical) 1 parameter =
        Data.Gaussian.Cast.Path.ofCoordinate parameter := by
      change (0 : Basic.Canonical) + Data.Gaussian.Cast.Path.ofCoordinate parameter * 1 = _
      rewrite [Basic.mul_one, Basic.zero_add]
      rfl
    have firstReading : (displacedPolynomial first).eval (Affine.line 0 1 parameter) =
        first.displacement * Gaussian.Evaluation.eval first.polynomial
          (Data.Gaussian.Cast.Path.ofCoordinate parameter) := by
      rewrite [displacedPolynomial, toDense_eval,
        Gaussian.Evaluation.eval_scale, unitParameter]
      rfl
    have lastReading : (displacedPolynomial last).eval (Affine.line 0 1 parameter) =
        last.displacement * Gaussian.Evaluation.eval last.polynomial
          (Data.Gaussian.Cast.Path.ofCoordinate parameter) := by
      rewrite [displacedPolynomial, toDense_eval,
        Gaussian.Evaluation.eval_scale, unitParameter]
      rfl
    rewrite [residualPolynomial, Dense.Basic.DensePolynomial.eval_sub, source.derivative_eq,
      firstReading, lastReading, ← displacement_eq]
    have difference : first.displacement *
          Gaussian.Evaluation.eval first.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter) -
        first.displacement *
          Gaussian.Evaluation.eval last.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter) =
        first.displacement *
          (Gaussian.Evaluation.eval first.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter) -
            Gaussian.Evaluation.eval last.polynomial (Data.Gaussian.Cast.Path.ofCoordinate parameter)) := by
      ring1
    rewrite [difference, Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded parameter inside)
      (Norm.Basic.normSq_nonneg _)
  let comparison := Comparison.ofBound last source.value (Norm.Basic.normSq first.displacement * bound) residual
  have estimate := comparison.integral_error_le
  change Norm.Basic.normSq (source.value.eval 1 - source.value.eval 0 - last.integralSample) ≤ _ at estimate
  rewrite [displacedPrimitive_increment first] at estimate
  exact estimate.trans_eq (by
    change 2 * (Norm.Basic.normSq first.displacement * bound) =
      2 * bound * Norm.Basic.normSq first.displacement
    ring1)

end Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
end
