import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk106

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard106_positionTrace (token : Unit) :
    (geometricShard106Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1696 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
