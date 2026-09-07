import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk108

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard108_positionTrace (token : Unit) :
    (geometricShard108Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1728 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
