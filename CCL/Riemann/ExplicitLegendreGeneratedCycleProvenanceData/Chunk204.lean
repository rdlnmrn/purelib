import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk204

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard204_positionTrace (token : Unit) :
    (geometricShard204Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3264 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
