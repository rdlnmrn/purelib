import CCL.Riemann.ExplicitLegendreGeneratedAPeriodState

/-!
# Scalar bounds for the sharp generated Legendre A-period

This module checkpoints the exact dyadic aggregate estimates used by the final
positive lower-bound certificates.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

def generatedSharpComparisonRadius : RFAP.ConstructiveFraction.Rational :=
  (Dyadic.mk 23 3).toCoordinate

theorem generatedSharpComparisonRadius_nonnegative :
    0 <= generatedSharpComparisonRadius := by
  have positive :
      (Dyadic.mk 0 0).toCoordinate < (Dyadic.mk 23 3).toCoordinate :=
    Dyadic.lt_sound (by decide)
  unfold generatedSharpComparisonRadius
  simpa only [Dyadic.toCoordinate_zero_numerator] using positive.le

def generatedMovementSqUpper : RFAP.ConstructiveFraction.Rational :=
  (Dyadic.mk 11 8).toCoordinate

theorem generatedMovementSqSum_le_upper :
    generatedMovementSqSum <=
      generatedMovementSqUpper := by
  unfold generatedMovementSqSum generatedMovementSqUpper
  exact Dyadic.le_sound (by decide +revert)

def generatedTransportWeightedErrorUpper :
    RFAP.ConstructiveFraction.Rational :=
  (Dyadic.mk 17 14).toCoordinate

theorem generatedTransportWeightedErrorUpper_eq :
    generatedTransportWeightedErrorUpper =
      (17 / 16384 : RFAP.ConstructiveFraction.Rational) := by
  unfold generatedTransportWeightedErrorUpper Dyadic.toCoordinate
    Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  rfl

theorem generatedTransportWeightedErrorSum_le_upper :
    generatedTransportWeightedErrorSum <=
      generatedTransportWeightedErrorUpper := by
  unfold generatedTransportWeightedErrorSum
  exact Dyadic.le_sound (by decide +revert)

private theorem generatedNatCast_nonnegative (value : Nat) :
    (0 : RFAP.ConstructiveFraction.Rational) <=
      (value : RFAP.ConstructiveFraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- Dyadic arithmetic for the deliberately coarse whole-path upper bound.
Keeping this expression on the certificate grid avoids normalizing a large
rational quotient in the kernel. -/
def generatedTransportAggregateUpperDyadic :
    CCL.Riemann.GeneratedLegendreCertificateData.Dyadic :=
  CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.scale 7680
    (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.add
      (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.scale 10
        (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.mul
          (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.mk 1 14)
          (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.mk 11 8)))
      (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.mk 17 14))

theorem generatedTransportAggregateUpper_eq :
    2 * (nonstationaryCellCount : RFAP.ConstructiveFraction.Rational) *
        (10 * generatedSharpTarget * generatedMovementSqUpper +
          generatedTransportWeightedErrorUpper) =
      generatedTransportAggregateUpperDyadic.toCoordinate := by
  unfold generatedTransportAggregateUpperDyadic generatedSharpTarget
    generatedMovementSqUpper generatedTransportWeightedErrorUpper
    nonstationaryCellCount
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    Dyadic.toCoordinate_scale, Dyadic.toCoordinate_mul]
  ring1

theorem generatedTransportAggregate_sharp_le_radiusSq :
    generatedTransportAggregate generatedSharpTarget <=
      generatedSharpComparisonRadius ^ 2 := by
  have movementTerm :
      10 * generatedSharpTarget * generatedMovementSqSum <=
        10 * generatedSharpTarget *
          generatedMovementSqUpper :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      generatedMovementSqSum_le_upper
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        generatedSharpTarget_positive.le)
  have inside :
      10 * generatedSharpTarget * generatedMovementSqSum +
          generatedTransportWeightedErrorSum <=
        10 * generatedSharpTarget *
            generatedMovementSqUpper +
          generatedTransportWeightedErrorUpper :=
    add_le_add movementTerm
      generatedTransportWeightedErrorSum_le_upper
  unfold generatedTransportAggregate
  calc
    2 * (nonstationaryCellCount : RFAP.ConstructiveFraction.Rational) *
          (10 * generatedSharpTarget * generatedMovementSqSum +
            generatedTransportWeightedErrorSum) <=
        2 * (nonstationaryCellCount : RFAP.ConstructiveFraction.Rational) *
          (10 * generatedSharpTarget * generatedMovementSqUpper +
            generatedTransportWeightedErrorUpper) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inside
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (generatedNatCast_nonnegative nonstationaryCellCount))
    _ <= generatedSharpComparisonRadius ^ 2 := by
      calc
        2 * (nonstationaryCellCount : RFAP.ConstructiveFraction.Rational) *
              (10 * generatedSharpTarget * generatedMovementSqUpper +
                generatedTransportWeightedErrorUpper) =
            generatedTransportAggregateUpperDyadic.toCoordinate :=
          generatedTransportAggregateUpper_eq
        _ <= (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.square
            (CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.mk 23 3)
          ).toCoordinate :=
          CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.le_sound
            (by decide +revert)
        _ = generatedSharpComparisonRadius ^ 2 := by
          unfold generatedSharpComparisonRadius
            CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.square
          rw [CCL.Riemann.GeneratedLegendreCertificateData.Dyadic.toCoordinate_mul]
          rw [pow_two]

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
