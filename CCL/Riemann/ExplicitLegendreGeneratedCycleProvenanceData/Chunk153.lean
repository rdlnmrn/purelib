import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk153

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard153_positionTrace (token : Unit) :
    (geometricShard153Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2448 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
