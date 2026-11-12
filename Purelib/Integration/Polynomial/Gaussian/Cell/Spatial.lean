module

import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Composition
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached spatial coefficients on original polynomial cells

One retained affine coordinate is shared by all coefficient pullbacks on an
original segment. Each pullback keeps the composed dense table and its exact
ascending conversion alongside the original integration cell that consumes it.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Spatial

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial
open Dense.Basic (DensePolynomial)
open Dense.Gaussian.Substitution

set_option genInjectivity false in
/-- The shared original affine-coordinate coefficient cache of a displayed segment. -/
structure Coordinate (start finish : Canonical) where
  /-- The actual retained difference of the original endpoints. -/
  displacement : Canonical
  /-- The retained displacement belongs to the original ordered endpoints. -/
  displacement_eq : displacement = finish - start
  /-- The cached dense affine-coordinate table. -/
  polynomial : DensePolynomial Canonical
  /-- The table retains the original displacement and starting coordinate in descending order. -/
  polynomial_eq : polynomial = ⟨[displacement, start]⟩

constructive_injectivity Coordinate

namespace Coordinate

/-- Cache the original segment displacement and affine-coordinate table once. -/
@[expose] def build (start finish : Canonical) : Coordinate start finish :=
  let displacement := finish - start
  ⟨displacement, rfl, ⟨[displacement, start]⟩, rfl⟩

/-- The retained coordinate cache reads the original spatial point at the supplied local parameter. -/
theorem eval {start finish : Canonical} (coordinate : Coordinate start finish) (parameter : Canonical) :
    coordinate.polynomial.eval parameter = start + parameter * (finish - start) := by
  rw [coordinate.polynomial_eq, coordinate.displacement_eq]
  change (0 * parameter + (finish - start)) * parameter + start = _
  ring1

end Coordinate

set_option genInjectivity false in
/-- A spatial coefficient pullback retained by the exact original integration cell.

The original source polynomial and shared coordinate cache index the view.
The local dense table is composed once and converted without normalization;
the same ascending table is consumed by the retained cell model. -/
structure Pullback {start finish : Canonical} (coordinate : Coordinate start finish)
    (source : DensePolynomial Canonical) (allowance : Rational) where
  /-- The composed dense table retained for this original source and coordinate. -/
  localPolynomial : DensePolynomial Canonical
  /-- The composed table consumes the actual source and the actual shared coordinate cache. -/
  localPolynomial_eq : localPolynomial = Composition.compose source coordinate.polynomial
  /-- The exact ascending coefficient table consumed by the original cell. -/
  ascending : Ascending.Gaussian.CoefficientPolynomial
  /-- The ascending conversion retains every coefficient of the same local dense table. -/
  ascending_eq : ascending = Ascending.Gaussian.Dense.Evaluation.fromDense localPolynomial
  /-- The original finite integration cell consuming these exact caches. -/
  model : Basic.CellModel
  /-- The model starts at the original displayed starting coordinate. -/
  start_eq : model.start = start
  /-- The model finishes at the original displayed finishing coordinate. -/
  finish_eq : model.finish = finish
  /-- The original integration cell consumes the retained ascending table. -/
  polynomial_eq : model.polynomial = ascending
  /-- The model retains the original requested local allowance. -/
  allowance_eq : model.localAllowance = allowance

constructive_injectivity Pullback

namespace Pullback

/-- Compose a spatial coefficient once and retain its exact conversion in the original integration cell. -/
@[expose] def build {start finish : Canonical} (coordinate : Coordinate start finish)
    (source : DensePolynomial Canonical) (allowance : Rational) (nonnegative : 0 ≤ allowance) :
    Pullback coordinate source allowance :=
  let localPolynomial := Composition.compose source coordinate.polynomial
  let ascending := Ascending.Gaussian.Dense.Evaluation.fromDense localPolynomial
  let model : Basic.CellModel := ⟨start, finish, ascending, allowance, nonnegative, []⟩
  ⟨localPolynomial, rfl, ascending, rfl, model, rfl, rfl, rfl, rfl⟩

/-- Read the original cell polynomial as the retained spatial coefficient at its actual segment point. -/
theorem eval_local {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) (parameter : Canonical) :
    Ascending.Gaussian.Evaluation.eval pullback.model.polynomial parameter =
      source.eval (start + parameter * (finish - start)) := by
  rw [pullback.polynomial_eq, pullback.ascending_eq, Ascending.Gaussian.Dense.Evaluation.fromDense_eval,
    pullback.localPolynomial_eq, Composition.eval_compose, coordinate.eval]

/-- The original cell displacement is exactly the retained shared-coordinate displacement. -/
theorem displacement_eq {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) : pullback.model.displacement = coordinate.displacement := by
  unfold Basic.CellModel.displacement
  rw [pullback.start_eq, pullback.finish_eq, coordinate.displacement_eq]

/-- The original pullback cell's weighted allowance uses its retained ordered displacement and local allowance. -/
theorem weightedAllowance_eq {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) :
    pullback.model.weightedAllowance = Canonical.normSq (finish - start) * allowance := by
  unfold Basic.CellModel.weightedAllowance
  rewrite [pullback.displacement_eq, coordinate.displacement_eq, pullback.allowance_eq]
  rfl

/-- The original cell integral consumes the exact retained ascending coefficient table and ordered endpoints. -/
theorem integralSample_eq {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) :
    pullback.model.integralSample = (finish - start) * Ascending.Gaussian.Integral.definiteIntegral
      pullback.ascending 0 1 := by
  unfold Basic.CellModel.integralSample Basic.CellModel.displacement
  rw [pullback.start_eq, pullback.finish_eq, pullback.polynomial_eq]

/-- An exact spatial primitive gives the original pullback cell's integral as its ordered endpoint difference.

The derivative law concerns the retained original source polynomial. Its
actual local coefficient readback makes the compiled derivative residual
zero, and the original finite primitive comparison forces exact agreement.
The original local table, allowance and model remain retained. -/
theorem integralSample_primitive {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) (value : DensePolynomial Canonical)
    (derivative : ∀ point, (Dense.Gaussian.GCD.derivative value).eval point = source.eval point) :
    pullback.model.integralSample = value.eval finish - value.eval start := by
  let comparison := Primitive.Comparison.ofSpatialBound pullback.model value 0 (by
    intro parameter _
    rewrite [pullback.start_eq, pullback.displacement_eq, coordinate.displacement_eq, derivative]
    change Purelib.Data.Gaussian.Norm.Basic.normSq
      ((finish - start) * (source.eval (start +
        Purelib.Data.Gaussian.Cast.Path.ofCoordinate parameter * (finish - start)) -
        Ascending.Gaussian.Evaluation.eval pullback.model.polynomial
          (Purelib.Data.Gaussian.Cast.Path.ofCoordinate parameter))) ≤ 0
    rewrite [pullback.eval_local, Purelib.Data.Gaussian.Basic.sub_self,
      Purelib.Data.Gaussian.Basic.mul_zero, Purelib.Data.Gaussian.Norm.Basic.normSq_zero]
    exact Purelib.Data.Rat.Fraction.Order.Basic.le_refl _)
  have estimate := comparison.integral_error_le
  change Purelib.Data.Gaussian.Norm.Basic.normSq
    ((Primitive.spatialPrimitive pullback.model value).eval 1 -
      (Primitive.spatialPrimitive pullback.model value).eval 0 - pullback.model.integralSample) ≤ 2 * 0 at estimate
  rewrite [Primitive.spatialPrimitive_finish, Primitive.spatialPrimitive_start,
    pullback.start_eq, pullback.finish_eq] at estimate
  have zero := Purelib.Data.Gaussian.Norm.Basic.normSq_eq_zero.mp
    (Purelib.Data.Rat.Fraction.Order.Basic.le_antisymm _ _ estimate
      (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg _))
  have equality := congrArg (fun scalar : Canonical => scalar + pullback.model.integralSample) zero
  calc
    pullback.model.integralSample = 0 + pullback.model.integralSample := by ring1
    _ = _ := equality.symm
    _ = value.eval finish - value.eval start := by ring1

end Pullback

end Purelib.Integration.Polynomial.Gaussian.Cell.Spatial

end
