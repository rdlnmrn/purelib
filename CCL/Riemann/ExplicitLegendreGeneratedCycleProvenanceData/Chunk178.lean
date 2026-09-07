import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk178

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard178_positionTrace (token : Unit) :
    (geometricShard178Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2848 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
