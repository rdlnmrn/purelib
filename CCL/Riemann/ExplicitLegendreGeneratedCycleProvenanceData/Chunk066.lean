import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk066

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard066_positionTrace (token : Unit) :
    (geometricShard066Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1056 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
