import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk210

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard210_positionTrace (token : Unit) :
    (geometricShard210Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3360 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
