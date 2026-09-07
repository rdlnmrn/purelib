import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk093

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard093_positionTrace (token : Unit) :
    (geometricShard093Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1488 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
