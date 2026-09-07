import CCL.Riemann.ExplicitLegendreGeneratedBPeriodLower

/-!
# Initial generated Legendre B-period lower bound

This module proves the headline positive lower certificate for the initial
sharp finite model.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedLegendreBCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

/-- Headline lower certificate for the sharply initialized generated
B-period. -/
theorem generatedSharpBPeriodProgram_initialRealLower (token : Unit) :
    generatedSharpRealLower <=
      ((generatedSharpBPeriodProgram token).integral.model
        0).integralSample.re := by
  unfold generatedSharpRealLower
  exact
    CCL.Riemann.PreparedSubdivisionModels.real_sub_radius_le_of_normSq_reverse_sub_le
      generatedSharpComparisonRadius_nonnegative
      ((generatedSharpInitial_difference_le token).trans
        generatedTransportAggregate_sharp_le_radiusSq)

theorem generatedSharpBPeriodProgram_initialReal_positive (token : Unit) :
    0 < ((generatedSharpBPeriodProgram token).integral.model
      0).integralSample.re :=
  generatedSharpRealLower_positive.trans_le
    (generatedSharpBPeriodProgram_initialRealLower token)

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
