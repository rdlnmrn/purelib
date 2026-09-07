import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk074

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard074_positionTrace (token : Unit) :
    (geometricShard074Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1184 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
