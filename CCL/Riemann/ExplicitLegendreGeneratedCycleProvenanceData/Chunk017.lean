import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk017

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard017_positionTrace (token : Unit) :
    (geometricShard017Summary token).range.run.positionTrace =
      PositionTrace.consecutive 272 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
