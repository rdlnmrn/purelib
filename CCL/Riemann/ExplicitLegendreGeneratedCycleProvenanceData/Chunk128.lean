import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk128

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard128_positionTrace (token : Unit) :
    (geometricShard128Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2048 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
