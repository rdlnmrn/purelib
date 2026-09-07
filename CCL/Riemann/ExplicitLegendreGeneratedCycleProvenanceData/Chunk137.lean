import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk137

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard137_positionTrace (token : Unit) :
    (geometricShard137Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2192 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
