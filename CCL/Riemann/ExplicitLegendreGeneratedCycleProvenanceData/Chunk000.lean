import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk000

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard000_positionTrace (token : Unit) :
    (geometricShard000Summary token).range.run.positionTrace =
      PositionTrace.consecutive 0 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
