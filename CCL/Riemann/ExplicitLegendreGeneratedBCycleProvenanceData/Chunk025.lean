import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk025

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard025_positionTrace (token : Unit) :
    (geometricShard025Summary token).range.run.positionTrace =
      PositionTrace.consecutive 200 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
