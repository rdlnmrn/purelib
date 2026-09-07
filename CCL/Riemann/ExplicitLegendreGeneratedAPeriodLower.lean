import CCL.Riemann.ExplicitLegendreGeneratedAPeriodBounds

/-!
# Sharp generated Legendre A-period lower bounds

This module packages the public initial, uniform-model, and coherent-sample
lower certificates from the prepared state and exact scalar bounds.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

def generatedSharpRealLower : RFAP.ConstructiveFraction.Rational :=
  literalSample.re - generatedSharpComparisonRadius

theorem generatedSharpRealLower_positive : 0 < generatedSharpRealLower := by
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
