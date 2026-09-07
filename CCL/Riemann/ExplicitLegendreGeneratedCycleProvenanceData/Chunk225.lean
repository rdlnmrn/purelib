import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk225

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard225_positionTrace (token : Unit) :
    (geometricShard225Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3600 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
