import CCL.Riemann.ExplicitLegendreGeneratedAPeriodBase

/-!
# Prepared sharp generated Legendre run

This module checkpoints the expensive finite transport preparation before the
sharp A-period state and its estimates are elaborated.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

/-- The generic transport constructor hides the potentially large child list
and all of its dependent proofs behind one non-indexed package. -/
def generatedSharpPreparedRun (token : Unit) : GeneratedTransportPreparedRun :=
  (generatedClosedRun token).prepareTransport generatedSharpTarget
    generatedSharpTarget_positive

@[simp] theorem generatedSharpPreparedRun_source (token : Unit) :
    (generatedSharpPreparedRun token).source = generatedClosedRun token := by
  unfold generatedSharpPreparedRun
  exact GeneratedCenteredRun.prepareTransport_source _ _ _

@[simp] theorem generatedSharpPreparedRun_target (token : Unit) :
    (generatedSharpPreparedRun token).target = generatedSharpTarget := by
  unfold generatedSharpPreparedRun
  exact GeneratedCenteredRun.prepareTransport_target _ _ _

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
