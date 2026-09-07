import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk034

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard034_positionTrace (token : Unit) :
    (geometricShard034Summary token).range.run.positionTrace =
      PositionTrace.consecutive 544 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
