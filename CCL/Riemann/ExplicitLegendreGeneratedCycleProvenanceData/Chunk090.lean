import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk090

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard090_positionTrace (token : Unit) :
    (geometricShard090Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1440 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
