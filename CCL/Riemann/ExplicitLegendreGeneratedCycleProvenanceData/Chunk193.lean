import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk193

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard193_positionTrace (token : Unit) :
    (geometricShard193Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3088 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
