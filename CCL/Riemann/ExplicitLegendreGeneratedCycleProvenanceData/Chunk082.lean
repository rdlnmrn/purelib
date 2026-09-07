import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk082

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard082_positionTrace (token : Unit) :
    (geometricShard082Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1312 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
