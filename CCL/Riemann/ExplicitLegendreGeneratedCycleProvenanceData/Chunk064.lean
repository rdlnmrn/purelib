import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk064

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard064_positionTrace (token : Unit) :
    (geometricShard064Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1024 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
