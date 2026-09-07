import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk182

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard182_positionTrace (token : Unit) :
    (geometricShard182Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2912 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
