import CCL.Riemann.ExplicitLegendreGeneratedAPeriodLower

/-!
# Initial generated Legendre A-period lower bound

This module proves the headline positive lower certificate for the initial
sharp finite model.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

/-- Headline lower certificate for the sharply initialized generated
A-period. -/
theorem generatedSharpAPeriodProgram_initialRealLower (token : Unit) :
    generatedSharpRealLower <=
      ((generatedSharpAPeriodProgram token).integral.model
        0).integralSample.re := by
  unfold generatedSharpRealLower
  exact
    CCL.Riemann.PreparedSubdivisionModels.real_sub_radius_le_of_normSq_reverse_sub_le
      generatedSharpComparisonRadius_nonnegative
      ((generatedSharpInitial_difference_le token).trans
        generatedTransportAggregate_sharp_le_radiusSq)

theorem generatedSharpAPeriodProgram_initialReal_positive (token : Unit) :
    0 < ((generatedSharpAPeriodProgram token).integral.model
      0).integralSample.re :=
  generatedSharpRealLower_positive.trans_le
    (generatedSharpAPeriodProgram_initialRealLower token)

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
