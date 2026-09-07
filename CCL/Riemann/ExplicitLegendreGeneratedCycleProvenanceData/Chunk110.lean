import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk110

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard110_positionTrace (token : Unit) :
    (geometricShard110Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1760 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
