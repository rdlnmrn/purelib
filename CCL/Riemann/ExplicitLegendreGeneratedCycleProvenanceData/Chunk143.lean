import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk143

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard143_positionTrace (token : Unit) :
    (geometricShard143Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2288 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
