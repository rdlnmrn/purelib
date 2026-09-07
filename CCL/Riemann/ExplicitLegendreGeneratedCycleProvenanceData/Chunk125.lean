import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk125

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard125_positionTrace (token : Unit) :
    (geometricShard125Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2000 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
