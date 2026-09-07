import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk120

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard120_positionTrace (token : Unit) :
    (geometricShard120Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1920 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
