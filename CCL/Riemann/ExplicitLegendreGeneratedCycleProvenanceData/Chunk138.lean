import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk138

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard138_positionTrace (token : Unit) :
    (geometricShard138Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2208 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
