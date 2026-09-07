import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk217

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard217_positionTrace (token : Unit) :
    (geometricShard217Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3472 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
