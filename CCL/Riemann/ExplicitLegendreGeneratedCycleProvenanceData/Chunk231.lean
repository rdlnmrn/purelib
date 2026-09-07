import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk231

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard231_positionTrace (token : Unit) :
    (geometricShard231Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3696 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
