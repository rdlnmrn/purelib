import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk025

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard025_positionTrace (token : Unit) :
    (geometricShard025Summary token).range.run.positionTrace =
      PositionTrace.consecutive 400 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
