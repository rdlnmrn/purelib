import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk000

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard000_positionTrace (token : Unit) :
    (geometricShard000Summary token).range.run.positionTrace =
      PositionTrace.consecutive 0 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
