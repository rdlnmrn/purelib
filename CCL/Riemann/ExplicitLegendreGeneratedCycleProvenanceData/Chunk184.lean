import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk184

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard184_positionTrace (token : Unit) :
    (geometricShard184Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2944 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
