import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk158

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard158_positionTrace (token : Unit) :
    (geometricShard158Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2528 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
