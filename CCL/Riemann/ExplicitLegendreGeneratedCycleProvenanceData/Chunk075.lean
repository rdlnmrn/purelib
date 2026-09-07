import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk075

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard075_positionTrace (token : Unit) :
    (geometricShard075Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1200 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
