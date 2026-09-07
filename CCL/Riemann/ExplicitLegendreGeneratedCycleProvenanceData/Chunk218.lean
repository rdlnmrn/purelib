import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk218

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard218_positionTrace (token : Unit) :
    (geometricShard218Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3488 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
