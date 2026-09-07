import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk115

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard115_positionTrace (token : Unit) :
    (geometricShard115Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1840 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
