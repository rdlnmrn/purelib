import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk161

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard161_positionTrace (token : Unit) :
    (geometricShard161Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2576 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
