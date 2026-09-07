import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk157

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard157_positionTrace (token : Unit) :
    (geometricShard157Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2512 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
