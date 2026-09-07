import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk114

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard114_positionTrace (token : Unit) :
    (geometricShard114Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1824 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
