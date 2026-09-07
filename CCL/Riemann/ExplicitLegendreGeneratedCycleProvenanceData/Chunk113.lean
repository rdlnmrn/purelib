import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk113

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard113_positionTrace (token : Unit) :
    (geometricShard113Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1808 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
