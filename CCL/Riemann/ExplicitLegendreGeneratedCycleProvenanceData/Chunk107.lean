import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk107

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard107_positionTrace (token : Unit) :
    (geometricShard107Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1712 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
