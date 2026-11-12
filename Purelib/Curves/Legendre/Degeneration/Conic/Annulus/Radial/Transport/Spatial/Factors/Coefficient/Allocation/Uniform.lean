module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation
public import Purelib.Data.Gaussian.Norm.Reciprocal.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Fixed finite cost ceilings from actual numerator and radius bounds

The actual fine Bound cache, original differential exponent and normalized
radius remain inputs. Ordinary nonnegative finite products propagate the
independently proved numerator/radius ceilings through the original four
allocation costs. This computes the cost bound; no final sample, request or
integral comparison is supplied as a hypothesis.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

namespace Uniform

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation

/-- The old-source coefficient expression with independently paid fixed numerator/radius ceilings. -/
private def sourceCeiling (value floor : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  2 * ((value * floor⁻¹ ^ exponent) * Norm.Reciprocal.powerSensitivity (1 / 4 : Fraction.Rational) exponent * 4)

/-- The normalized-factor coefficient expression on the SAME fixed positive radius floor. -/
private def normalCeiling (value floor : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  2 * (2 * (value * Norm.Reciprocal.powerSensitivity floor exponent * (4 * (9 * floor)⁻¹)) *
    (1 / 4 : Fraction.Rational)⁻¹ ^ exponent)

/-- The spatial coefficient expression retaining the original actual quadratic sensitivity. -/
private def spatialCeiling (value slope floor sensitivity : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  2 * (2 * (slope * floor⁻¹ ^ exponent +
    value * Norm.Reciprocal.powerSensitivity floor exponent * (2 * sensitivity * (9 * floor)⁻¹)) *
      (1 / 4 : Fraction.Rational)⁻¹ ^ exponent +
    (value * floor⁻¹ ^ exponent) * Norm.Reciprocal.powerSensitivity (1 / 4 : Fraction.Rational) exponent * 2)

/-- The original full-product arithmetic expression with a fixed actual numerator and positive product floor. -/
private def arithmeticCeiling (value floor : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  1 + (value * Norm.Reciprocal.powerSensitivity (floor / 4) exponent) / 8

/-- Compute one nonnegative fixed ceiling for the original four allocation costs at the SAME finite exponent. -/
def costCeiling (value slope floor sensitivity : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  max 0 (4 * (sourceCeiling value floor exponent + normalCeiling value floor exponent +
    spatialCeiling value slope floor sensitivity exponent) + 4 * arithmeticCeiling value floor exponent + 7)

/-- The fixed cost has an explicit nonnegative floor, independently of any later observation. -/
theorem costCeiling_nonnegative (value slope floor sensitivity : Fraction.Rational) (exponent : Nat) :
    0 ≤ costCeiling value slope floor sensitivity exponent :=
  Fraction.Order.Basic.le_max_left _ _

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- Actual original numerator and radius bounds derive a fixed ceiling on every fine allocation cost.

The positive radius floor and both numerator inequalities are local
geometric/cache evidence. The actual fine normalized radius, source Anchor,
original finite exponent and retained numerator fold remain unchanged.
-/
theorem cost_le (bounds : Bounds data anchor) {value slope floor : Fraction.Rational}
    (floorPositive : 0 < floor) (radiusLower : floor ≤ anchor.seed.separation.radius ^ 2)
    (valueBound : bounds.value ≤ value) (slopeBound : bounds.slope ≤ slope) :
    cost bounds ≤ costCeiling value slope floor (Segment.Reading.Payment.sensitivity site parameter)
      differential.denominatorExponent := by
  have two : (0 : Fraction.Rational) ≤ 2 := of_decide_eq_true rfl
  have four : (0 : Fraction.Rational) ≤ 4 := of_decide_eq_true rfl
  have radiusPositive := normalFloor_positive anchor
  have valueNonnegative := bounds.nonnegative.1.trans valueBound
  have radiusInverse := (Fraction.Order.Field.inv_pos_direct radiusPositive).1
  have inverse := Fraction.Order.Field.inv_le_inv_of_pos_direct floorPositive radiusLower
  have powers := Arithmetic.pow_le_pow_direct radiusInverse inverse differential.denominatorExponent
  have radiusPower := Arithmetic.pow_nonneg_direct radiusInverse differential.denominatorExponent
  have unitPositive : (0 : Fraction.Rational) < 1 / 4 := of_decide_eq_true rfl
  have unitPower := Arithmetic.pow_nonneg_direct
    (Fraction.Order.Field.inv_pos_direct unitPositive).1 differential.denominatorExponent
  have unitSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative unitPositive differential.denominatorExponent
  have sensitivity := Norm.Reciprocal.powerSensitivity_antitone floorPositive radiusLower
    differential.denominatorExponent
  have radiusSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative radiusPositive
    differential.denominatorExponent
  have floorSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative floorPositive
    differential.denominatorExponent
  have sumPositive := Arithmetic.mul_pos_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 9) floorPositive
  have sumOrder := Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLower
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 9)
  have sumInverse := Fraction.Order.Field.inv_le_inv_of_pos_direct sumPositive sumOrder
  have sumRadiusPositive := Arithmetic.mul_pos_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 9) radiusPositive
  have sumRadiusInverse := (Fraction.Order.Field.inv_pos_direct sumRadiusPositive).1
  have valuePower := Arithmetic.mul_le_mul_direct valueBound powers radiusPower valueNonnegative
  have slopePower := Arithmetic.mul_le_mul_direct slopeBound powers radiusPower
    (bounds.nonnegative.2.trans slopeBound)
  have valueSensitivity := Arithmetic.mul_le_mul_direct valueBound sensitivity
    radiusSensitivity valueNonnegative
  have sensitivityFloorNonnegative := Arithmetic.mul_nonneg_direct
    valueNonnegative floorSensitivity
  have normalTerm := Arithmetic.mul_le_mul_direct valueSensitivity
    (Arithmetic.mul_le_mul_of_nonneg_left_direct sumInverse four)
    (Arithmetic.mul_nonneg_direct four sumRadiusInverse) sensitivityFloorNonnegative
  have physicalNonnegative := Arithmetic.mul_nonneg_direct two
    (Segment.Reading.Payment.sensitivity_nonnegative site parameter)
  have spatialTerm := Arithmetic.mul_le_mul_direct valueSensitivity
    (Arithmetic.mul_le_mul_of_nonneg_left_direct sumInverse physicalNonnegative)
    (Arithmetic.mul_nonneg_direct physicalNonnegative sumRadiusInverse) sensitivityFloorNonnegative
  have unitTerm := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_right_direct valuePower unitSensitivity) two
  have sourcePaid : sourceCoefficient bounds ≤ sourceCeiling value floor differential.denominatorExponent :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct valuePower unitSensitivity) four) two
  have normalPaid : normalCoefficient bounds ≤ normalCeiling value floor differential.denominatorExponent :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct normalTerm two) unitPower) two
  have spatialPaid : spatialCoefficient bounds ≤ spatialCeiling value slope floor
      (Segment.Reading.Payment.sensitivity site parameter) differential.denominatorExponent :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct slopePower spatialTerm) two) unitPower) unitTerm) two
  have productPositive := Fraction.Order.Field.div_pos_direct floorPositive
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 4)
  have productOrder := Fraction.Order.Field.divide_mono radiusLower
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 4)
  have fullSensitivity := Norm.Reciprocal.powerSensitivity_antitone productPositive productOrder
    differential.denominatorExponent
  have fullRadiusSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative
    (Fraction.Order.Field.div_pos_direct radiusPositive (of_decide_eq_true rfl : (0 : Fraction.Rational) < 4))
    differential.denominatorExponent
  have arithmeticPaid : Allocation.arithmeticCeiling bounds ≤
      arithmeticCeiling value floor differential.denominatorExponent :=
    Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Fraction.Rational))
      (Fraction.Order.Field.divide_mono
        (Arithmetic.mul_le_mul_direct valueBound fullSensitivity fullRadiusSensitivity
          valueNonnegative) (of_decide_eq_true rfl : (0 : Fraction.Rational) < 8))
  have raw := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          (Arithmetic.add_le_add_direct sourcePaid normalPaid) spatialPaid) four)
      (Arithmetic.mul_le_mul_of_nonneg_left_direct arithmeticPaid four))
    (Fraction.Order.Basic.le_refl (7 : Fraction.Rational))
  exact raw.trans (Fraction.Order.Basic.le_max_right _ _)

end Uniform

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

end
