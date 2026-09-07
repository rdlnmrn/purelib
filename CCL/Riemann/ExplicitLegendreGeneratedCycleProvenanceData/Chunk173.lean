import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk173

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard173_positionTrace (token : Unit) :
    (geometricShard173Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2768 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
