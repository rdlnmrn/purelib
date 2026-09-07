import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk092

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard092_positionTrace (token : Unit) :
    (geometricShard092Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1472 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
