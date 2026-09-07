import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk094

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard094_positionTrace (token : Unit) :
    (geometricShard094Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1504 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
