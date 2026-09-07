import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk095

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard095_positionTrace (token : Unit) :
    (geometricShard095Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1520 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
