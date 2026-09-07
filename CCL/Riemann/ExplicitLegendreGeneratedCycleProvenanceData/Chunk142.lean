import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk142

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard142_positionTrace (token : Unit) :
    (geometricShard142Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2272 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
