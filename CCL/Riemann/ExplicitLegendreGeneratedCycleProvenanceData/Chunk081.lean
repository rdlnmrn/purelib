import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk081

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard081_positionTrace (token : Unit) :
    (geometricShard081Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1296 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
