module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Quadratic.Split
import Purelib.Tactic.Ring

/-! # A fixed positive geometric cap below every finer Anchor's actual spatial request

The original finer radii stay within fixed half-gap-dependent bounds. Their
actual spatial coefficients therefore have one finite upper bound, and the
retained floor has a fixed positive lower bound. The resulting positive
request is paid by every original finer request without replacing any Seed,
window, Owner or factor budget. It is independent of the new chart depth.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment

namespace Uniform

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

/-- The original finer normalized radius-square floor depends only on the fixed original half-gap. -/
@[expose] def radiusFloor (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (9 / 128) * Norm.Basic.normSq (halfGap site parameter)

/-- The original ordinate quadrance bounds every finer actual normalized radius square from above. -/
@[expose] def radiusCeiling (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (25 / 16) * Norm.Basic.normSq (halfGap site parameter)

/-- The fixed original regular parameter makes the common radius floor strictly positive. -/
theorem radiusFloor_positive (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    0 < radiusFloor site parameter :=
  Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 9) (by decide +kernel))
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide +kernel)))
    (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero
      (by decide +kernel : (2 : Canonical) ≠ 0) regular.symm))

/-- Both fixed original radius bounds are nonnegative. -/
theorem radii_nonnegative (site : Fin 2) (parameter : Canonical) :
    0 ≤ radiusFloor site parameter ∧ 0 ≤ radiusCeiling site parameter :=
  ⟨Arithmetic.mul_nonneg_direct
      (Fraction.Order.Field.div_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 9) (Nat.zero_le 9))
        (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 128) (Nat.zero_le 128)))
      (Norm.Basic.normSq_nonneg _),
    Arithmetic.mul_nonneg_direct
      (Fraction.Order.Field.div_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 25) (Nat.zero_le 25))
        (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 16) (Nat.zero_le 16)))
      (Norm.Basic.normSq_nonneg _)⟩

/-- The original two geometric sensitivity terms have one fixed finer-depth-independent upper coefficient. -/
@[expose] def spatialCeiling (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (9 / 2) * sensitivity site parameter / radiusFloor site parameter + 80 * radiusCeiling site parameter

/-- The fixed original sensitivity and radius bounds make the spatial ceiling nonnegative. -/
theorem spatialCeiling_nonnegative (site : Fin 2) (parameter : Canonical) :
    0 ≤ spatialCeiling site parameter := by
  unfold spatialCeiling
  have normal : (0 : Fraction.Rational) ≤
      (9 / 2) * sensitivity site parameter / radiusFloor site parameter :=
    Fraction.Order.Field.div_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Fraction.Order.Field.div_nonneg_direct
          (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 9) (Nat.zero_le 9))
          (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 2) (Nat.zero_le 2)))
        (sensitivity_nonnegative site parameter)) (radii_nonnegative site parameter).1
  have unit : (0 : Fraction.Rational) ≤ 80 * radiusCeiling site parameter :=
    Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 80 by decide +kernel)
      (radii_nonnegative site parameter).2
  have combined := Arithmetic.add_le_add_direct normal unit
  exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le combined

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside}

/-- Every genuine finer Anchor's actual geometric coefficient obeys the SAME fixed sensitivity ceiling. -/
theorem spatialCoefficient_le (anchor : Parameter.Anchor source.lift) :
    spatialCoefficient anchor ≤ spatialCeiling site parameter := by
  have radii := Clearance.Envelope.radius_bounds anchor
  have numerator := Arithmetic.mul_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 9 / 2) (sensitivity_nonnegative site parameter)
  have normal := Fraction.Order.Field.div_le_div_of_nonneg_left_direct numerator
    (radiusFloor_positive site parameter anchor.regular) radii.1
  have unit := Arithmetic.mul_le_mul_of_nonneg_left_direct radii.2
    (show (0 : Fraction.Rational) ≤ 80 from Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 80)
      (Nat.zero_le 80))
  unfold spatialCoefficient spatialCeiling
  rewrite [unitCeiling_eq]
  exact Arithmetic.add_le_add_direct normal unit

/-- Compute one positive original physical request that remains below every finer Anchor's geometric cap. -/
def spatialRequest (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    AccuracyRequest :=
  ⟨(radiusFloor site parameter / 4) / (8 * (1 + spatialCeiling site parameter)),
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct (radiusFloor_positive site parameter regular) (of_decide_eq_true rfl))
      (Arithmetic.mul_pos_direct (of_decide_eq_true rfl)
        (Arithmetic.add_pos_of_pos_of_nonneg_direct
          (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (spatialCeiling_nonnegative site parameter)))⟩

/-- The SAME fixed request fits every genuine finer actual spatial request, preserving its original floor/Seed. -/
theorem spatialRequest_le (anchor : Parameter.Anchor source.lift) :
    (spatialRequest site parameter anchor.regular).tolerance ≤ (Payment.spatialRequest anchor).tolerance := by
  rewrite [Payment.spatialRequest_tolerance anchor]
  have radii := Clearance.Envelope.radius_bounds anchor
  have floorLower := Fraction.Order.Field.divide_mono radii.1
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 4)
  have ceiling := spatialCoefficient_le anchor
  have enlarge : spatialCeiling site parameter ≤ 1 + spatialCeiling site parameter := by
    exact (Fraction.Field.zero_add _).symm.trans_le
      (Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _))
  have denominator := Arithmetic.mul_le_mul_of_nonneg_left_direct (ceiling.trans enlarge)
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 8)
  have largePositive := Arithmetic.mul_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 8)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (spatialCeiling_nonnegative site parameter))
  have smallPositive := Arithmetic.mul_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 8)
    (spatialCoefficient_positive anchor)
  have numerator := Fraction.Order.Field.divide_mono floorLower largePositive
  have quotient := Fraction.Order.Field.div_le_div_of_nonneg_left_direct (floor_positive anchor).le
    smallPositive denominator
  exact numerator.trans quotient

end Uniform

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment

end
