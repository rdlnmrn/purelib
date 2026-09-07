import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk048

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard048_positionTrace (token : Unit) :
    (geometricShard048Summary token).range.run.positionTrace =
      PositionTrace.consecutive 768 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
