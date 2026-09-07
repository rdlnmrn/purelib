import CCL.Riemann.ExplicitLegendreGeneratedAPeriodInitial

/-!
# Finite-model propagation for generated Legendre A-period bounds

The general real-coordinate estimate is elaborated independently of the large
generated path.  The Legendre specialization can then instantiate this
compact theorem without expanding its concrete finite model.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

/-- An initial real lower bound loses at most `radius` at any later model of a
finite refinement program whose error scale is bounded by `radius ^ 2`. -/
theorem refinementProgram_laterRealLower
    (program : CCL.ProgressiveGaussianIntegration.RefinementProgram)
    (lower radius : RFAP.ConstructiveFraction.Rational)
    (radiusNonnegative : 0 <= radius)
    (initialLower : lower <= (program.model 0).integralSample.re)
    (errorScaleLe : program.errorScale <= radius ^ 2)
    (index : Nat) :
    lower - radius <= (program.model index).integralSample.re := by
  have movement :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((program.model index).integralSample -
            (program.model 0).integralSample) <=
        radius ^ 2 := by
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((program.model index).integralSample -
            (program.model 0).integralSample) <=
          CCL.FiniteGeometric.quarterRadius program.errorScale 0 :=
        program.later_close (Nat.zero_le index)
      _ = program.errorScale := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct]
      _ <= radius ^ 2 := errorScaleLe
  calc
    lower - radius <= (program.model 0).integralSample.re - radius :=
      RFAP.ConstructiveFraction.sub_le_sub_right_direct initialLower radius
    _ <= (program.model index).integralSample.re :=
      CCL.Riemann.PreparedSubdivisionModels.real_sub_radius_le_of_normSq_reverse_sub_le
        radiusNonnegative movement

/-- A uniform positive real lower bound survives every later finite model;
the entire sharp source process moves by squared distance at most one
quarter from its already positive initial model. -/
def generatedSharpUniformRealLower : RFAP.ConstructiveFraction.Rational :=
  generatedSharpRealLower - 1 / 2

theorem generatedSharpUniformRealLower_positive :
    0 < generatedSharpUniformRealLower := by
  decide +revert

theorem generatedSharpAPeriodProgram_errorScale (token : Unit) :
    (generatedSharpAPeriodProgram token).integral.errorScale =
      generatedSharpSourceErrorScale := by
  change (generatedSharpInitialState token).sourceIntegral.errorScale = _
  exact generatedSharpInitialState_sourceIntegral_errorScale token

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
