import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk037

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard037_positionTrace (token : Unit) :
    (geometricShard037Summary token).range.run.positionTrace =
      PositionTrace.consecutive 592 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
