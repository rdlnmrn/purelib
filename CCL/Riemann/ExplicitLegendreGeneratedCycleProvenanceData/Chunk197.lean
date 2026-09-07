import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk197

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard197_positionTrace (token : Unit) :
    (geometricShard197Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3152 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
