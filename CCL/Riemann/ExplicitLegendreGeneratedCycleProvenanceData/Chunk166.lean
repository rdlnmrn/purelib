import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk166

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard166_positionTrace (token : Unit) :
    (geometricShard166Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2656 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
