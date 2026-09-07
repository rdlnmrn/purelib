import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk198

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard198_positionTrace (token : Unit) :
    (geometricShard198Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3168 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
