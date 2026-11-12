module

public import Purelib.Algebra.Monogenic.Coordinates.Reading.Parameters
public import Purelib.Algebra.Monogenic.Coordinates.Multiplication
public import Purelib.Algebra.Ring.GaussianReading
-- The exposed reader retains the original scalar nonnegativity certificates.
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Gaussian readings of original cyclic algebras

The original coordinate evaluator extends a retained parent reading at a
bounded Gaussian candidate. Its gain is fixed in advance, and its uniform
multiplication error is linear in the actual parent error and original
generator-column residual.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- Scalar collection of the original finite power and product discrepancy estimates. -/
private theorem product_error_formula (factor multiplier powerWeight parentGain parentError powerCeiling
    generatorWeight growthTotal residual : Rational) :
    factor * 2 * ((factor * parentError * powerCeiling) * multiplier * powerWeight +
      parentGain * ((2 * (factor * parentGain * residual +
        (factor * factor * parentError * powerCeiling) * generatorWeight)) * multiplier * powerWeight * growthTotal)) =
      parentFactorValue factor multiplier powerWeight parentGain powerCeiling generatorWeight growthTotal *
        parentError +
        sourceFactorValue factor multiplier powerWeight parentGain growthTotal * residual := by
  unfold parentFactorValue sourceFactorValue
  ring0

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}
variable {cyclic : Cyclic generator} {parent : Weight K} {embed : Canonical → K} {parentGain radius : Rational}

namespace Parameters

/-- The original coordinate reading satisfies the cached candidate-independent gain bound. -/
theorem gain_bound (parameters : Parameters cyclic parent parentGain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = parentGain)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius) (value : Element cyclic) :
    Norm.Basic.normSq (evaluate reading.read point value) ≤
      parameters.gain * (Element.weight cyclic parent).value value := by
  have coefficients (coefficient : K) :
      Norm.Basic.normSq (reading.read coefficient) ≤ parentGain * parent.value coefficient :=
    gain_eq ▸ reading.gainBound coefficient
  have retained := evaluate_normSq_le parent reading.read reading.mapZero parentGain parameters.powers.powerTotal
    parameters.parentGainNonnegative parameters.powers.powerTotal_nonnegative coefficients point
    (parameters.powers.normSq_pow_le point pointBound) value
  rewrite [← parameters.factor_eq] at retained
  exact retained.trans (congrArg (fun gain : Rational => gain * (Element.weight cyclic parent).value value)
    parameters.gain_eq.symm).le

/-- The original child reading has the cached linear bound in the actual parent error and source residual.

Generator columns use the same original matrix. Finite power propagation and
coordinate reconstruction consume the stored original weight and radius
tables; no new matrix power or original division is computed by this proof.
-/
theorem product_bound (parameters : Parameters cyclic parent parentGain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = parentGain)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Rational) (residualNonnegative : 0 ≤ residual)
    (residualBound : ∀ column : Fin dimension,
      Norm.Basic.normSq (sumFin (fun row => reading.read (generator row column) * point ^ row.val) -
        point * point ^ column.val) ≤ residual) (left right : Element cyclic) :
    Norm.Basic.normSq (evaluate reading.read point (left * right) -
        evaluate reading.read point left * evaluate reading.read point right) ≤
      (parameters.parentFactor * reading.error + parameters.sourceFactor * residual) *
        (Element.weight cyclic parent).value left * (Element.weight cyclic parent).value right := by
  let lifted := Element.weight cyclic parent
  let ceiling := parameters.powers.powerTotal
  let step := 2 * (parameters.factor * parentGain * residual +
    (parameters.factor * parameters.factor * reading.error * ceiling) * parameters.weights.generatorWeight)
  let scalarError := parameters.factor * reading.error * ceiling
  let powerError := step * parameters.multiplier * parameters.weights.powerTotal * parameters.powers.growthTotal
  have coefficients (coefficient : K) :
      Norm.Basic.normSq (reading.read coefficient) ≤ parentGain * parent.value coefficient :=
    gain_eq ▸ reading.gainBound coefficient
  have scalarErrorNonnegative : 0 ≤ scalarError := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct parameters.factor_nonnegative reading.errorNonnegative)
    parameters.powers.powerTotal_nonnegative
  have stepNonnegative : 0 ≤ step := by
    have first : 0 ≤ parameters.factor * parentGain * residual := Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct parameters.factor_nonnegative parameters.parentGainNonnegative)
      residualNonnegative
    have second : 0 ≤ (parameters.factor * parameters.factor * reading.error * ceiling) *
        parameters.weights.generatorWeight := by
      repeat' first
        | exact parameters.factor_nonnegative
        | exact reading.errorNonnegative
        | exact parameters.powers.powerTotal_nonnegative
        | exact parameters.weights.generatorWeight_nonnegative
        | apply Order.Arithmetic.mul_nonneg_direct
    exact Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
      (Order.Arithmetic.add_le_add_direct first second)
  have powerFactorNonnegative : 0 ≤ step * parameters.multiplier * parameters.weights.powerTotal :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct stepNonnegative parameters.multiplier_nonnegative)
      parameters.weights.powerTotal_nonnegative
  have powerErrorNonnegative : 0 ≤ powerError :=
    Order.Arithmetic.mul_nonneg_direct powerFactorNonnegative parameters.powers.growthTotal_nonnegative
  have stepBound (value : Element cyclic) : Norm.Basic.normSq
      (evaluate reading.read point (root cyclic * value) - point * evaluate reading.read point value) ≤
        step * lifted.value value := by
    have retained := evaluate_root_mul_normSq_sub_le parent reading.read reading.mapZero reading.mapAdd
      parentGain reading.error ceiling residual parameters.parentGainNonnegative reading.errorNonnegative
      residualNonnegative coefficients reading.productBound point
      (parameters.powers.normSq_pow_le point pointBound) residualBound value
    rewrite [← parameters.factor_eq, ← parameters.weights.generatorWeight_eq] at retained
    exact retained
  have scalarBound (coefficient : K) (value : Element cyclic) : Norm.Basic.normSq
      (evaluate reading.read point (scalar cyclic coefficient * value) -
        reading.read coefficient * evaluate reading.read point value) ≤
          scalarError * parent.value coefficient * lifted.value value := by
    have retained := evaluate_scalar_mul_normSq_sub_le parent reading.read reading.mapZero reading.error ceiling
      reading.errorNonnegative parameters.powers.powerTotal_nonnegative reading.productBound point
      (parameters.powers.normSq_pow_le point pointBound) coefficient value
    rewrite [← parameters.factor_eq] at retained
    exact retained
  have powerBound (index : Fin dimension) (value : Element cyclic) : Norm.Basic.normSq
      (evaluate reading.read point (root cyclic ^ index.val * value) -
        point ^ index.val * evaluate reading.read point value) ≤ powerError * lifted.value value := by
    have retained := evaluate_root_pow_mul_normSq_sub_le parent reading.read point step parameters.weights.powerTotal
      radius stepNonnegative parameters.weights.powerTotal_nonnegative parameters.powers.nonnegative pointBound
      parameters.weights.root_power_weight_le stepBound index.val (Nat.le_of_lt index.isLt) value
    rewrite [← parameters.multiplier_eq] at retained
    exact retained.trans (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (parameters.powers.growth_pow_le_total index)
        powerFactorNonnegative) (lifted.nonnegative value))
  have retained := evaluate_mul_normSq_sub_le parent reading.read reading.mapZero reading.mapAdd point parentGain
    scalarError powerError parameters.weights.powerTotal parameters.parentGainNonnegative scalarErrorNonnegative
    powerErrorNonnegative parameters.weights.powerTotal_nonnegative coefficients parameters.weights.root_power_weight_le
    scalarBound powerBound left right
  rewrite [← parameters.factor_eq, ← parameters.multiplier_eq] at retained
  have formula := product_error_formula parameters.factor parameters.multiplier parameters.weights.powerTotal
    parentGain reading.error ceiling parameters.weights.generatorWeight parameters.powers.growthTotal residual
  rewrite [← parameters.parentFactor_eq, ← parameters.sourceFactor_eq] at formula
  exact retained.trans (congrArg (fun coefficient : Rational => coefficient * lifted.value left * lifted.value right)
    formula).le

/-- Construct the original Gaussian coordinate reading with its fixed gain and certified linear multiplication error.

The original parent reading is captured once. The supplied candidate and its
original column residual certificate determine the child error; the retained
parameter caches were prepared independently of either observation.
-/
@[expose] def toReading (parameters : Parameters cyclic parent parentGain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = parentGain)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Rational) (residualNonnegative : 0 ≤ residual)
    (residualBound : ∀ column : Fin dimension,
      Norm.Basic.normSq (sumFin (fun row => reading.read (generator row column) * point ^ row.val) -
        point * point ^ column.val) ≤ residual) :
    GaussianReading (Element.weight cyclic parent) (fun coefficient => scalar cyclic (embed coefficient)) where
  read := evaluate reading.read point
  mapZero := evaluate_zero reading.read reading.mapZero point
  mapOne := (congrArg (evaluate reading.read point) (scalar_one cyclic)).symm.trans
    ((evaluate_scalar reading.read reading.mapZero point 1).trans reading.mapOne)
  mapAdd := evaluate_add reading.read reading.mapZero reading.mapAdd point
  mapNeg := evaluate_neg reading.read reading.mapZero reading.mapNeg point
  mapScalarMul coefficient value := evaluate_scalar_mul reading.read reading.mapZero point (embed coefficient)
    coefficient (reading.mapScalarMul coefficient) value
  gain := parameters.gain
  gainNonnegative := parameters.gain_nonnegative
  gainBound := parameters.gain_bound reading gain_eq point pointBound
  error := parameters.parentFactor * reading.error + parameters.sourceFactor * residual
  errorNonnegative := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.mul_nonneg_direct parameters.parentFactor_nonnegative reading.errorNonnegative)
    (Order.Arithmetic.mul_nonneg_direct parameters.sourceFactor_nonnegative residualNonnegative)
  productBound := parameters.product_bound reading gain_eq point pointBound residual residualNonnegative residualBound

end Parameters

end Purelib.Algebra.Monogenic.Cyclic.Element.Reading

end
