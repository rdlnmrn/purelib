import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk131

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard131_positionTrace (token : Unit) :
    (geometricShard131Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2096 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
