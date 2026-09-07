import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk024

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard024_positionTrace (token : Unit) :
    (geometricShard024Summary token).range.run.positionTrace =
      PositionTrace.consecutive 192 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
