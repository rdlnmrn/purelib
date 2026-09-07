import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk088

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard088_positionTrace (token : Unit) :
    (geometricShard088Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1408 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
