import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk239

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard239_positionTrace (token : Unit) :
    (geometricShard239Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3824 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
