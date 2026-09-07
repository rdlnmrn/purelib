import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk023

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard023_positionTrace (token : Unit) :
    (geometricShard023Summary token).range.run.positionTrace =
      PositionTrace.consecutive 368 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
