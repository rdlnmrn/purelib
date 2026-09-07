import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk171

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard171_positionTrace (token : Unit) :
    (geometricShard171Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2736 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
