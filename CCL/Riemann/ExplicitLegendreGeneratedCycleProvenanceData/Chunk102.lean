import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk102

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard102_positionTrace (token : Unit) :
    (geometricShard102Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1632 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
