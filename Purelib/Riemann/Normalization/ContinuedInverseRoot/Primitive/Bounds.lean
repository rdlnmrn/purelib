module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stage-independent primitive reading ceilings

The original point's parameter reciprocal and norm are computed once. Bounds
for the same retained inverse-model square, cube and fifth power use the same
root witness and residual; all refinement rates concern the actual stage.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation.Rational

variable {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}

set_option genInjectivity false in
/-- Cached exact scalar factors and uniform odd-reading scales at one original continued point.

The parameter reciprocal retains the source polynomial and point. All
ceilings use the original root floor, initial model residual and inverse-error
scale, without building a later inverse polynomial or selecting a new root. -/
structure PrimitiveBounds (sample : Point patch point) where
  /-- The actual retained original continued point owner. -/
  owner : Point patch point
  /-- The retained owner is the original input. -/
  owner_eq : owner = sample
  /-- The cached reciprocal of the source's original positive root-norm floor. -/
  lowerInverse : Fraction.Rational
  /-- The cached reciprocal uses the original retained floor. -/
  lowerInverse_eq : lowerInverse = patch.rootLower⁻¹
  /-- The cached reciprocal of the exact original point parameter. -/
  parameterInverse : Canonical
  /-- The parameter inverse belongs to the original polynomial and original coordinate. -/
  parameterInverse_eq : parameterInverse = (polynomial.eval point)⁻¹
  /-- The cached squared norm of that same original parameter reciprocal. -/
  inverseNorm : Fraction.Rational
  /-- The cached norm reads the retained actual parameter inverse. -/
  inverseNorm_eq : inverseNorm = Norm.Basic.normSq parameterInverse
  /-- The cached uniform ceiling for the same inverse-model value. -/
  valueCeiling : Fraction.Rational
  /-- The value ceiling uses the original inverse-error scale and root floor. -/
  valueCeiling_eq : valueCeiling = 2 * (patch.inverseErrorScale + lowerInverse)
  /-- The cached geometric scale for the divided-generator inverse reading. -/
  inverseScale : Fraction.Rational
  /-- The inverse scale charges both original inverse error and actual root square residual. -/
  inverseScale_eq : inverseScale = 2 * (patch.inverseErrorScale +
    lowerInverse * ((1 / 4096) * sample.parameterNorm) * inverseNorm)
  /-- The cached geometric scale for the same retained cubic inverse-model reading. -/
  cubeScale : Fraction.Rational
  /-- The cubic scale uses the same inverse and initial residual ceilings. -/
  cubeScale_eq : cubeScale = 2 * (inverseScale + valueCeiling * patch.base.model.bound) * inverseNorm
  /-- The cached geometric scale for the same retained fifth-power reading. -/
  fifthScale : Fraction.Rational
  /-- The fifth scale retains both contributions of the original residual polynomial. -/
  fifthScale_eq : fifthScale =
    2 * (inverseScale + valueCeiling * ((8 + 2 * patch.base.model.bound) * patch.base.model.bound)) * inverseNorm ^ 2

constructive_injectivity PrimitiveBounds

/-- Compute the original point's scalar denominator factors and all three odd-reading scales once. -/
@[expose] def primitiveBounds (sample : Point patch point) : PrimitiveBounds sample :=
  let lowerInverse := patch.rootLower⁻¹
  let parameterInverse := (polynomial.eval point)⁻¹
  let inverseNorm := Norm.Basic.normSq parameterInverse
  let valueCeiling := 2 * (patch.inverseErrorScale + lowerInverse)
  let inverseScale := 2 * (patch.inverseErrorScale +
    lowerInverse * ((1 / 4096) * sample.parameterNorm) * inverseNorm)
  let cubeScale := 2 * (inverseScale + valueCeiling * patch.base.model.bound) * inverseNorm
  let fifthScale :=
    2 * (inverseScale + valueCeiling * ((8 + 2 * patch.base.model.bound) * patch.base.model.bound)) * inverseNorm ^ 2
  ⟨sample, rfl, lowerInverse, rfl, parameterInverse, rfl, inverseNorm, rfl, valueCeiling, rfl,
    inverseScale, rfl, cubeScale, rfl, fifthScale, rfl⟩

namespace PrimitiveBounds

variable {sample : Point patch point}

/-- The retained reciprocal of the original positive root floor is nonnegative. -/
theorem lowerInverse_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.lowerInverse := by
  rewrite [bounds.lowerInverse_eq]
  exact (Fraction.Order.Field.inv_pos_direct patch.rootLower_positive).le

/-- The retained squared norm of the actual source parameter inverse is nonnegative. -/
theorem inverseNorm_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.inverseNorm := by
  rewrite [bounds.inverseNorm_eq]
  exact Norm.Basic.normSq_nonneg _

/-- The retained uniform inverse-model value ceiling is nonnegative. -/
theorem valueCeiling_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.valueCeiling := by
  rewrite [bounds.valueCeiling_eq]
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg patch.inverseErrorScale_positive.le bounds.lowerInverse_nonnegative)

/-- The retained inverse-reading scale charges nonnegative original source quantities. -/
theorem inverseScale_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.inverseScale := by
  rewrite [bounds.inverseScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg patch.inverseErrorScale_positive.le
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct bounds.lowerInverse_nonnegative
          (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) sample.parameterNorm_positive.le))
        bounds.inverseNorm_nonnegative))

/-- The retained cubic-reading scale is nonnegative. -/
theorem cubeScale_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.cubeScale := by
  rewrite [bounds.cubeScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg bounds.inverseScale_nonnegative
        (Order.Arithmetic.mul_nonneg_direct
          bounds.valueCeiling_nonnegative patch.base.model.bound_nonnegative)))
    bounds.inverseNorm_nonnegative

/-- The retained fifth-power reading scale is nonnegative. -/
theorem fifthScale_nonnegative (bounds : PrimitiveBounds sample) : 0 ≤ bounds.fifthScale := by
  rewrite [bounds.fifthScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg bounds.inverseScale_nonnegative
        (Order.Arithmetic.mul_nonneg_direct bounds.valueCeiling_nonnegative
          (Order.Arithmetic.mul_nonneg_direct
            (add_nonneg (by decide)
              (Order.Arithmetic.mul_nonneg_direct (by decide) patch.base.model.bound_nonnegative))
            patch.base.model.bound_nonnegative))))
    (Order.Arithmetic.sq_nonneg_direct _)

end PrimitiveBounds

namespace PrimitiveReading

variable {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
    {powers : OddPowers model.value}

/-- The same shared root's exact divided-generator error has the retained geometric inverse scale. -/
theorem generator_error_le_scale (reading : PrimitiveReading sample depth model powers)
    (bounds : PrimitiveBounds sample) (inside : patch.box.Contains point) :
    Norm.Basic.normSq (reading.inverse - reading.root * bounds.parameterInverse) ≤
      Geometric.Basic.quarterRadius bounds.inverseScale depth := by
  rewrite [bounds.parameterInverse_eq]
  have estimate := reading.generator_error_le inside
  have scalar : reading.generatorBound = Geometric.Basic.quarterRadius bounds.inverseScale depth := by
    rewrite [generatorBound, Geometric.Basic.quarterRadius_eq_mul_pow, bounds.inverseScale_eq,
      bounds.lowerInverse_eq, bounds.inverseNorm_eq, bounds.parameterInverse_eq, relativeRootError,
      Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact estimate.trans_eq scalar

/-- The cached cubic readback consumes the exact original inverse-model scalar evaluation. -/
theorem cube_readback (reading : PrimitiveReading sample depth model powers) : reading.cube = reading.inverse ^ 3 := by
  rewrite [reading.cube_eq, powers.cube_eval, ← reading.inverse_eq]
  rfl

/-- The cached fifth-power readback consumes the same original scalar evaluation. -/
theorem fifth_readback (reading : PrimitiveReading sample depth model powers) :
    reading.fifth = reading.inverse ^ 5 := by
  rewrite [reading.fifth_eq, powers.fifth_eval, ← reading.inverse_eq]
  rfl

/-- The cached residual has the defining equation of the same original inverse reading. -/
theorem residual_readback (reading : PrimitiveReading sample depth model powers) :
    reading.residual = 1 - polynomial.eval point * reading.inverse ^ 2 := by
  rewrite [reading.residual_eq, model.residual_eq, ← reading.inverse_eq]
  rfl

/-- The cubic reading's exact discrepancy is the inverse discrepancy divided once more, minus its own residual term. -/
theorem cube_difference (reading : PrimitiveReading sample depth model powers) (bounds : PrimitiveBounds sample) :
    reading.cube - reading.root * bounds.parameterInverse ^ 2 =
      (reading.inverse - reading.root * bounds.parameterInverse) * bounds.parameterInverse -
        reading.inverse * reading.residual * bounds.parameterInverse := by
  have parameterUnit := Algebra.Field.ExplicitField.mul_inv_cancel (polynomial.eval point) sample.owner.parameterNonzero
  rewrite [reading.cube_readback, reading.residual_readback, bounds.parameterInverse_eq]
  calc
    _ = reading.inverse ^ 3 * (polynomial.eval point * (polynomial.eval point)⁻¹) -
        reading.root * ((polynomial.eval point)⁻¹) ^ 2 := by rewrite [parameterUnit]; ring1
    _ = _ := by ring1

/-- The actual cached cubic reading obeys the retained stage-independent geometric scale. -/
theorem cube_error_le_scale (reading : PrimitiveReading sample depth model powers)
    (bounds : PrimitiveBounds sample) (inside : patch.box.Contains point) :
    Norm.Basic.normSq (reading.cube - reading.root * bounds.parameterInverse ^ 2) ≤
      Geometric.Basic.quarterRadius bounds.cubeScale depth := by
  have inverseBound := reading.generator_error_le_scale bounds inside
  have valueBound := reading.inverse_norm_le inside
  rewrite [← bounds.lowerInverse_eq, ← bounds.valueCeiling_eq] at valueBound
  have residualBound := reading.residual_le inside
  have first : Norm.Basic.normSq
      ((reading.inverse - reading.root * bounds.parameterInverse) * bounds.parameterInverse) ≤
      Geometric.Basic.quarterRadius bounds.inverseScale depth * bounds.inverseNorm := by
    rewrite [Norm.Basic.normSq_mul, ← bounds.inverseNorm_eq]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inverseBound bounds.inverseNorm_nonnegative
  have second : Norm.Basic.normSq (reading.inverse * reading.residual * bounds.parameterInverse) ≤
      bounds.valueCeiling * Geometric.Basic.quarterRadius patch.base.model.bound depth * bounds.inverseNorm := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, ← bounds.inverseNorm_eq]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.mul_le_mul_direct valueBound residualBound
        (Norm.Basic.normSq_nonneg _) bounds.valueCeiling_nonnegative) bounds.inverseNorm_nonnegative
  rewrite [reading.cube_difference bounds]
  have estimate := (Norm.Bounds.normSq_sub_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first second) (by decide))
  exact estimate.trans_eq (by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow, bounds.cubeScale_eq]
    ring1)

/-- The actual fifth-power discrepancy retains both the linear and squared source residual contributions. -/
theorem fifth_difference (reading : PrimitiveReading sample depth model powers) (bounds : PrimitiveBounds sample) :
    reading.fifth - reading.root * bounds.parameterInverse ^ 3 =
      (reading.inverse - reading.root * bounds.parameterInverse) * bounds.parameterInverse ^ 2 -
        reading.inverse * (2 * reading.residual - reading.residual ^ 2) * bounds.parameterInverse ^ 2 := by
  have parameterUnit := Algebra.Field.ExplicitField.mul_inv_cancel (polynomial.eval point) sample.owner.parameterNonzero
  rewrite [reading.fifth_readback, reading.residual_readback, bounds.parameterInverse_eq]
  calc
    _ = reading.inverse ^ 5 * (polynomial.eval point * (polynomial.eval point)⁻¹) ^ 2 -
        reading.root * ((polynomial.eval point)⁻¹) ^ 3 := by rewrite [parameterUnit]; ring1
    _ = _ := by ring1

/-- The residual polynomial entering the actual fifth-power discrepancy has a geometric source ceiling. -/
theorem double_residual_error_le (reading : PrimitiveReading sample depth model powers)
    (inside : patch.box.Contains point) :
    Norm.Basic.normSq (2 * reading.residual - reading.residual ^ 2) ≤
      (8 + 2 * patch.base.model.bound) * Geometric.Basic.quarterRadius patch.base.model.bound depth := by
  have residualBound := reading.residual_le inside
  have small := (Geometric.Basic.quarterRadius_le_scale patch.base.model.bound_nonnegative depth)
  have first : Norm.Basic.normSq (2 * reading.residual) ≤
      4 * Geometric.Basic.quarterRadius patch.base.model.bound depth := by
    rewrite [Norm.Basic.normSq_mul, show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct residualBound (by decide)
  have second : Norm.Basic.normSq (reading.residual ^ 2) ≤
      patch.base.model.bound * Geometric.Basic.quarterRadius patch.base.model.bound depth := by
    rewrite [Power.normSq_pow, pow_two]
    exact Order.Arithmetic.mul_le_mul_direct (residualBound.trans small) residualBound
      (Norm.Basic.normSq_nonneg _) patch.base.model.bound_nonnegative
  exact ((Norm.Bounds.normSq_sub_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first second) (by decide))).trans_eq
      (by ring1)

/-- The cached fifth-power reading obeys the original source's retained geometric scale. -/
theorem fifth_error_le_scale (reading : PrimitiveReading sample depth model powers)
    (bounds : PrimitiveBounds sample) (inside : patch.box.Contains point) :
    Norm.Basic.normSq (reading.fifth - reading.root * bounds.parameterInverse ^ 3) ≤
      Geometric.Basic.quarterRadius bounds.fifthScale depth := by
  have inverseBound := reading.generator_error_le_scale bounds inside
  have valueBound := reading.inverse_norm_le inside
  rewrite [← bounds.lowerInverse_eq, ← bounds.valueCeiling_eq] at valueBound
  have residualBound := reading.double_residual_error_le inside
  have squareNorm : Norm.Basic.normSq (bounds.parameterInverse ^ 2) = bounds.inverseNorm ^ 2 := by
    rewrite [Power.normSq_pow, bounds.inverseNorm_eq]
    rfl
  have first : Norm.Basic.normSq
      ((reading.inverse - reading.root * bounds.parameterInverse) * bounds.parameterInverse ^ 2) ≤
      Geometric.Basic.quarterRadius bounds.inverseScale depth * bounds.inverseNorm ^ 2 := by
    rewrite [Norm.Basic.normSq_mul, squareNorm]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inverseBound
      (Order.Arithmetic.sq_nonneg_direct _)
  have second : Norm.Basic.normSq
      (reading.inverse * (2 * reading.residual - reading.residual ^ 2) * bounds.parameterInverse ^ 2) ≤
      bounds.valueCeiling * ((8 + 2 * patch.base.model.bound) *
        Geometric.Basic.quarterRadius patch.base.model.bound depth) * bounds.inverseNorm ^ 2 := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, squareNorm]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.mul_le_mul_direct valueBound residualBound
        (Norm.Basic.normSq_nonneg _) bounds.valueCeiling_nonnegative)
      (Order.Arithmetic.sq_nonneg_direct _)
  rewrite [reading.fifth_difference bounds]
  have estimate := (Norm.Bounds.normSq_sub_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first second) (by decide))
  exact estimate.trans_eq (by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow, bounds.fifthScale_eq]
    ring1)

end PrimitiveReading

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
