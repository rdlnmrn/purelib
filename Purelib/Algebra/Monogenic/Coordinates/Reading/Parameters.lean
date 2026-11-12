module

public import Purelib.Algebra.Monogenic.Cyclic.Weights
public import Purelib.Data.Gaussian.Power.Radius
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original finite parameters for cyclic Gaussian readings

The same generator weights, retained power weights and fixed-radius scans
determine the next gain and two error coefficients before a candidate is
observed. These constants are independent of the eventual parent error and
the observed polynomial residual.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element.Reading

open Purelib.Algebra.Ring (Weight)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- The cyclic reading gain from its finite sum factor and original coefficient gain. -/
@[expose] def gainValue (factor parentGain powerCeiling : Rational) : Rational :=
  factor * parentGain * powerCeiling

/-- The coefficient of the parent multiplication error in the next original cyclic reading. -/
@[expose] def parentFactorValue (factor multiplier powerWeight parentGain powerCeiling generatorWeight
    growthTotal : Rational) : Rational :=
  2 * factor * multiplier * powerWeight *
    (factor * powerCeiling + 2 * parentGain * factor * factor * powerCeiling * generatorWeight * growthTotal)

/-- The coefficient of the generator-column residual in the next original cyclic reading. -/
@[expose] def sourceFactorValue (factor multiplier powerWeight parentGain growthTotal : Rational) : Rational :=
  4 * factor * factor * parentGain * parentGain * multiplier * powerWeight * growthTotal

/-- Nonnegative original factors give a nonnegative parent-error coefficient. -/
theorem parentFactorValue_nonnegative {factor multiplier powerWeight parentGain powerCeiling generatorWeight
    growthTotal : Rational} (factorNonnegative : 0 ≤ factor) (multiplierNonnegative : 0 ≤ multiplier)
    (powerWeightNonnegative : 0 ≤ powerWeight) (parentGainNonnegative : 0 ≤ parentGain)
    (powerCeilingNonnegative : 0 ≤ powerCeiling) (generatorWeightNonnegative : 0 ≤ generatorWeight)
    (growthTotalNonnegative : 0 ≤ growthTotal) :
    0 ≤ parentFactorValue factor multiplier powerWeight parentGain powerCeiling generatorWeight growthTotal := by
  have twoNonnegative : (0 : Rational) ≤ 2 := by decide
  have firstNonnegative : 0 ≤ factor * powerCeiling :=
    Order.Arithmetic.mul_nonneg_direct factorNonnegative powerCeilingNonnegative
  have secondNonnegative : 0 ≤ 2 * parentGain * factor * factor * powerCeiling * generatorWeight * growthTotal :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct
          (Order.Arithmetic.mul_nonneg_direct
            (Order.Arithmetic.mul_nonneg_direct
              (Order.Arithmetic.mul_nonneg_direct twoNonnegative parentGainNonnegative)
              factorNonnegative)
            factorNonnegative)
          powerCeilingNonnegative)
        generatorWeightNonnegative)
      growthTotalNonnegative
  have sumNonnegative : 0 ≤ factor * powerCeiling +
      2 * parentGain * factor * factor * powerCeiling * generatorWeight * growthTotal :=
    Order.Arithmetic.add_le_add_direct firstNonnegative secondNonnegative
  unfold parentFactorValue
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct twoNonnegative factorNonnegative)
        multiplierNonnegative)
      powerWeightNonnegative)
    sumNonnegative

/-- Nonnegative original factors give a nonnegative source-residual coefficient. -/
theorem sourceFactorValue_nonnegative {factor multiplier powerWeight parentGain growthTotal : Rational}
    (factorNonnegative : 0 ≤ factor) (multiplierNonnegative : 0 ≤ multiplier)
    (powerWeightNonnegative : 0 ≤ powerWeight) (parentGainNonnegative : 0 ≤ parentGain)
    (growthTotalNonnegative : 0 ≤ growthTotal) :
    0 ≤ sourceFactorValue factor multiplier powerWeight parentGain growthTotal := by
  have fourNonnegative : (0 : Rational) ≤ 4 := by decide
  unfold sourceFactorValue
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct
          (Order.Arithmetic.mul_nonneg_direct
            (Order.Arithmetic.mul_nonneg_direct
              (Order.Arithmetic.mul_nonneg_direct fourNonnegative factorNonnegative)
              factorNonnegative)
            parentGainNonnegative)
          parentGainNonnegative)
        multiplierNonnegative)
      powerWeightNonnegative)
    growthTotalNonnegative

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}

set_option genInjectivity false in
/-- Cached original matrix and radius data with the fixed gain and linear error coefficients they determine.

The parent weight, fixed parent gain and fixed squared radius remain indices.
The original cached tables and every computed scalar are retained together
with their defining equalities; no candidate or observed residual is an input.
-/
structure Parameters (cyclic : Cyclic generator) (parent : Weight K) (parentGain radius : Rational) where
  /-- The fixed parent gain is nonnegative. -/
  parentGainNonnegative : 0 ≤ parentGain
  /-- The same original generator and power weights. -/
  weights : Cyclic.Weights cyclic parent
  /-- The same fixed-radius finite power and growth scans. -/
  powers : Power.Radius dimension radius
  /-- The once-computed squared finite-sum factor. -/
  factor : Rational
  /-- The factor uses the original cyclic dimension. -/
  factor_eq : factor = 2 ^ dimension
  /-- The once-computed multiplier of the same original lifted weight. -/
  multiplier : Rational
  /-- The multiplier has the original lifted-weight specification. -/
  multiplier_eq : multiplier = (Element.weight cyclic parent).multiplier
  /-- The retained gain for this original cyclic reading. -/
  gain : Rational
  /-- The gain consumes the original stored radius total. -/
  gain_eq : gain = gainValue factor parentGain powers.powerTotal
  /-- The retained coefficient multiplying the eventual parent error. -/
  parentFactor : Rational
  /-- The parent coefficient consumes the same original cached data. -/
  parentFactor_eq : parentFactor = parentFactorValue factor multiplier weights.powerTotal parentGain
    powers.powerTotal weights.generatorWeight powers.growthTotal
  /-- The retained coefficient multiplying the eventual generator-column residual. -/
  sourceFactor : Rational
  /-- The source coefficient consumes the same original cached data. -/
  sourceFactor_eq : sourceFactor = sourceFactorValue factor multiplier weights.powerTotal parentGain powers.growthTotal

constructive_injectivity Parameters

namespace Parameters

/-- Prepare the original finite caches and all fixed reading constants before observing a candidate. -/
@[expose] def prepare (cyclic : Cyclic generator) (parent : Weight K) (parentGain radius : Rational)
    (parentGainNonnegative : 0 ≤ parentGain) (radiusNonnegative : 0 ≤ radius) :
    Parameters cyclic parent parentGain radius :=
  let weights := Cyclic.Weights.prepare cyclic parent
  let powers := Power.Radius.prepare dimension radius radiusNonnegative
  let factor : Rational := 2 ^ dimension
  let multiplier := factor * parent.multiplier
  { parentGainNonnegative
    weights
    powers
    factor
    factor_eq := rfl
    multiplier
    multiplier_eq := rfl
    gain := gainValue factor parentGain powers.powerTotal
    gain_eq := rfl
    parentFactor := parentFactorValue factor multiplier weights.powerTotal parentGain
      powers.powerTotal weights.generatorWeight powers.growthTotal
    parentFactor_eq := rfl
    sourceFactor := sourceFactorValue factor multiplier weights.powerTotal parentGain powers.growthTotal
    sourceFactor_eq := rfl }

variable {cyclic : Cyclic generator} {parent : Weight K} {parentGain radius : Rational}

/-- The stored finite-sum factor is nonnegative. -/
theorem factor_nonnegative (parameters : Parameters cyclic parent parentGain radius) : 0 ≤ parameters.factor := by
  rewrite [parameters.factor_eq]
  exact Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension

/-- The stored original lifted-weight multiplier is nonnegative. -/
theorem multiplier_nonnegative (parameters : Parameters cyclic parent parentGain radius) :
    0 ≤ parameters.multiplier := by
  rewrite [parameters.multiplier_eq]
  exact (Element.weight cyclic parent).multiplier_nonnegative

/-- The stored original gain is nonnegative. -/
theorem gain_nonnegative (parameters : Parameters cyclic parent parentGain radius) : 0 ≤ parameters.gain := by
  rewrite [parameters.gain_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct parameters.factor_nonnegative parameters.parentGainNonnegative)
    parameters.powers.powerTotal_nonnegative

/-- The stored parent-error coefficient is nonnegative. -/
theorem parentFactor_nonnegative (parameters : Parameters cyclic parent parentGain radius) :
    0 ≤ parameters.parentFactor := by
  rewrite [parameters.parentFactor_eq]
  exact parentFactorValue_nonnegative parameters.factor_nonnegative parameters.multiplier_nonnegative
    parameters.weights.powerTotal_nonnegative parameters.parentGainNonnegative
    parameters.powers.powerTotal_nonnegative parameters.weights.generatorWeight_nonnegative
    parameters.powers.growthTotal_nonnegative

/-- The stored source-residual coefficient is nonnegative. -/
theorem sourceFactor_nonnegative (parameters : Parameters cyclic parent parentGain radius) :
    0 ≤ parameters.sourceFactor := by
  rewrite [parameters.sourceFactor_eq]
  exact sourceFactorValue_nonnegative parameters.factor_nonnegative parameters.multiplier_nonnegative
    parameters.weights.powerTotal_nonnegative parameters.parentGainNonnegative parameters.powers.growthTotal_nonnegative

end Parameters

end Purelib.Algebra.Monogenic.Cyclic.Element.Reading

end
