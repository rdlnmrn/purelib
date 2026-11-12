module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Observations
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # A coefficient-computed common request before physical factor observations

The original retained numerator fold and signed denominator windows compute
the spatial, residual and arithmetic coefficients. Their positive common
request pays a chosen free tolerance while preserving the separate cost of
an already supplied curved-source observation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient

namespace Allocation

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- The coefficient of the unchanged old curved-source residual in the actual spatial variation formula. -/
@[expose] def sourceCoefficient (bounds : Bounds data anchor) : Fraction.Rational :=
  2 * ((bounds.value * (anchor.seed.separation.radius ^ 2)⁻¹ ^ differential.denominatorExponent) *
    Norm.Reciprocal.powerSensitivity (1 / 4 : Fraction.Rational) differential.denominatorExponent * 4)

/-- The coefficient of the actual normalized query's independent square residual. -/
@[expose] def normalCoefficient (bounds : Bounds data anchor) : Fraction.Rational :=
  2 * (2 * (bounds.value *
    Norm.Reciprocal.powerSensitivity (anchor.seed.separation.radius ^ 2) differential.denominatorExponent *
      (4 * (9 * anchor.seed.separation.radius ^ 2)⁻¹)) *
    (1 / 4 : Fraction.Rational)⁻¹ ^ differential.denominatorExponent)

/-- The coefficient of actual squared displacement from the old curved source to its physical query. -/
@[expose] def spatialCoefficient (bounds : Bounds data anchor) : Fraction.Rational :=
  2 * (2 * (bounds.slope * (anchor.seed.separation.radius ^ 2)⁻¹ ^ differential.denominatorExponent +
    bounds.value * Norm.Reciprocal.powerSensitivity (anchor.seed.separation.radius ^ 2)
      differential.denominatorExponent *
        (2 * ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) *
          (9 * anchor.seed.separation.radius ^ 2)⁻¹)) *
            (1 / 4 : Fraction.Rational)⁻¹ ^ differential.denominatorExponent +
    (bounds.value * (anchor.seed.separation.radius ^ 2)⁻¹ ^ differential.denominatorExponent) *
      Norm.Reciprocal.powerSensitivity (1 / 4 : Fraction.Rational) differential.denominatorExponent * 2)

/-- The exact spatial variation is affine in both original residual requests and actual squared displacement. -/
theorem variation_eq (bounds : Bounds data anchor) (old unit normal : AccuracyRequest)
    (displacement : Fraction.Rational) : variationBound bounds old unit normal displacement =
      sourceCoefficient bounds * old.tolerance + sourceCoefficient bounds * unit.tolerance +
        normalCoefficient bounds * normal.tolerance + spatialCoefficient bounds * displacement := by
  unfold variationBound sourceCoefficient normalCoefficient spatialCoefficient normalMovement unitMovement
  simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
  ring1

/-- Every actual residual/spatial coefficient is nonnegative on the unchanged original signed windows. -/
theorem coefficients_nonnegative (bounds : Bounds data anchor) :
    0 ≤ sourceCoefficient bounds ∧ 0 ≤ normalCoefficient bounds ∧ 0 ≤ spatialCoefficient bounds := by
  have two : (0 : Fraction.Rational) ≤ 2 := of_decide_eq_true rfl
  have four : (0 : Fraction.Rational) ≤ 4 := of_decide_eq_true rfl
  have rPositive := normalFloor_positive anchor
  have rPower := Arithmetic.pow_nonneg_direct
    (Fraction.Order.Field.inv_pos_direct rPositive).le differential.denominatorExponent
  have unitPower := Arithmetic.pow_nonneg_direct
    (Fraction.Order.Field.inv_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 4)).le
    differential.denominatorExponent
  have normalSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative rPositive differential.denominatorExponent
  have unitSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 4) differential.denominatorExponent
  have sumInverse := (Fraction.Order.Field.inv_pos_direct
    (Arithmetic.mul_pos_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 9) rPositive)).le
  have numeratorPower := Arithmetic.mul_nonneg_direct bounds.nonnegative.1 rPower
  have numeratorSensitivity := Arithmetic.mul_nonneg_direct bounds.nonnegative.1 normalSensitivity
  have spatialSensitivity := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 801 / 64)
    (Norm.Basic.normSq_nonneg (halfGap site parameter))
  refine ⟨?_, ?_, ?_⟩
  · exact Arithmetic.mul_nonneg_direct two
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct numeratorPower unitSensitivity) four)
  · exact Arithmetic.mul_nonneg_direct two
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct two
          (Arithmetic.mul_nonneg_direct numeratorSensitivity
            (Arithmetic.mul_nonneg_direct four sumInverse))) unitPower)
  · apply Arithmetic.mul_nonneg_direct two
    change (0 : Fraction.Rational) + 0 ≤ _
    apply Arithmetic.add_le_add_direct
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct two
          (Arithmetic.add_le_add_direct
            (Arithmetic.mul_nonneg_direct bounds.nonnegative.2 rPower)
            (Arithmetic.mul_nonneg_direct numeratorSensitivity
              (Arithmetic.mul_nonneg_direct
                (Arithmetic.mul_nonneg_direct two spatialSensitivity) sumInverse)))) unitPower
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct numeratorPower unitSensitivity) two

/-- The same numerator cache and full-cubic floor bound the new arithmetic allowance independently of its root owner. -/
@[expose] def arithmeticCeiling (bounds : Bounds data anchor) : Fraction.Rational :=
  1 + (bounds.value * Norm.Reciprocal.powerSensitivity (anchor.seed.separation.radius ^ 2 / 4)
    differential.denominatorExponent) / 8

/-- The cached arithmetic ceiling is nonnegative on the actual original positive full-root floor. -/
theorem arithmeticCeiling_nonnegative (bounds : Bounds data anchor) : 0 ≤ arithmeticCeiling bounds :=
  Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
    (Fraction.Order.Field.div_nonneg_direct
      (Arithmetic.mul_nonneg_direct bounds.nonnegative.1
        (Norm.Reciprocal.powerSensitivity_nonnegative
          (Segment.Reading.Payment.floor_positive anchor) differential.denominatorExponent))
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 8))

/-- One finite coefficient pays the actual scalar point comparison's new spatial, factor, arithmetic and model costs. -/
@[expose] def cost (bounds : Bounds data anchor) : Fraction.Rational :=
  4 * (sourceCoefficient bounds + normalCoefficient bounds + spatialCoefficient bounds) +
    4 * arithmeticCeiling bounds + 7

/-- All terms of the computed common new-work coefficient are nonnegative. -/
theorem cost_nonnegative (bounds : Bounds data anchor) : 0 ≤ cost bounds :=
  Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
        (Arithmetic.add_le_add_direct
          (Arithmetic.add_le_add_direct (coefficients_nonnegative bounds).1
            (coefficients_nonnegative bounds).2.1) (coefficients_nonnegative bounds).2.2))
      (Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
        (arithmeticCeiling_nonnegative bounds))) (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 7)

/-- Compute a positive new-work tolerance from the chosen target and original cached coefficient costs. -/
def work (bounds : Bounds data anchor) (target : AccuracyRequest) : AccuracyRequest :=
  ⟨target.tolerance / (1 + cost bounds), Fraction.Order.Field.div_pos_direct target.positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (cost_nonnegative bounds))⟩

/-- The computed work tolerance pays its complete finite coefficient without changing any old observation. -/
theorem work_payment (bounds : Bounds data anchor) (target : AccuracyRequest) :
    cost bounds * (work bounds target).tolerance ≤ target.tolerance := by
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (cost_nonnegative bounds)
  have ratio : cost bounds / (1 + cost bounds) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
    exact (Fraction.Field.zero_add (cost bounds)).symm.trans_le
      ((Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _)).trans_eq (Fraction.Field.one_mul _).symm)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct ratio target.positive.le
  exact (show cost bounds * (work bounds target).tolerance =
    target.tolerance * (cost bounds / (1 + cost bounds)) by
      change cost bounds * (target.tolerance / (1 + cost bounds)) = _
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le (scaled.trans_eq (Fraction.Field.mul_one_direct _))

/-- The SAME computed work also pays the unchanged geometric physical-displacement ceiling. -/
def request (bounds : Bounds data anchor) (target : AccuracyRequest) : AccuracyRequest :=
  (work bounds target).minimum (Segment.Reading.Payment.spatialRequest anchor)

/-- The actual common request has the exact computed scalar minimum of the new-work and geometric tolerances. -/
theorem request_tolerance (bounds : Bounds data anchor) (target : AccuracyRequest) :
    (request bounds target).tolerance = min (target.tolerance / (1 + cost bounds))
      (Segment.Reading.Payment.spatialRequest anchor).tolerance := by
  rfl

/-- The actual common request retains its original new-work coefficient payment. -/
theorem request_payment (bounds : Bounds data anchor) (target : AccuracyRequest) :
    cost bounds * (request bounds target).tolerance ≤ target.tolerance :=
  (Arithmetic.mul_le_mul_of_nonneg_left_direct
    ((work bounds target).minimum_le_left _) (cost_nonnegative bounds)).trans (work_payment bounds target)

/-- The SAME common request meets the independently computed geometric physical-displacement ceiling. -/
theorem request_spatial_le (bounds : Bounds data anchor) (target : AccuracyRequest) :
    (request bounds target).tolerance ≤ (Segment.Reading.Payment.spatialRequest anchor).tolerance :=
  (work bounds target).minimum_le_right _

/-- The SAME retained numerator cache and signed full-root floor bound the original root-observation allowance. -/
theorem allowance_le (bounds : Bounds data anchor) {point rootParameter : Canonical}
    (inside : (sourceBox anchor).Contains point) (certificate : CertifiedSquareRoot.Certificate rootParameter) :
    Observation.Cache.allowanceFactor differential point certificate
      (anchor.seed.separation.radius ^ 2 / 4) ≤ arithmeticCeiling bounds := by
  have positive : 0 < anchor.seed.separation.radius ^ 2 / 4 := Segment.Reading.Payment.floor_positive anchor
  have magnitude := bounds.normSq_le inside
  have sensitivity := Arithmetic.mul_le_mul_of_nonneg_right_direct magnitude
    (Norm.Reciprocal.powerSensitivity_nonnegative positive differential.denominatorExponent)
  have identity : Observation.Cache.sensitivity differential point
      (anchor.seed.separation.radius ^ 2 / 4) =
      Norm.Basic.normSq (differential.scale * differential.numerator.eval point) *
        Norm.Reciprocal.powerSensitivity (anchor.seed.separation.radius ^ 2 / 4)
          differential.denominatorExponent := by
    unfold Observation.Cache.sensitivity Norm.Reciprocal.powerSensitivity
    ring1
  rewrite [← identity] at sensitivity
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct sensitivity
    (Fraction.Order.Field.inv_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 8)).le
  apply (Observation.Cache.allowanceFactor_le_sensitivity differential point certificate positive).trans
  unfold arithmeticCeiling
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  exact Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) scaled

end Allocation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient

end
