import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk124

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard124_positionTrace (token : Unit) :
    (geometricShard124Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1984 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
