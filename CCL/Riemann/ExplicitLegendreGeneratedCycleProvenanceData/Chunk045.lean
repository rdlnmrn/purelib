import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk045

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard045_positionTrace (token : Unit) :
    (geometricShard045Summary token).range.run.positionTrace =
      PositionTrace.consecutive 720 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
