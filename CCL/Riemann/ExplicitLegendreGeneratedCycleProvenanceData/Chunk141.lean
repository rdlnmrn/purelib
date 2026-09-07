import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk141

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard141_positionTrace (token : Unit) :
    (geometricShard141Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2256 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
