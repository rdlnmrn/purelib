import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk221

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard221_positionTrace (token : Unit) :
    (geometricShard221Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3536 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
