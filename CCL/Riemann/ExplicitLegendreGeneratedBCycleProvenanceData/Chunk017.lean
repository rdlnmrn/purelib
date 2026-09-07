import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk017

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard017_positionTrace (token : Unit) :
    (geometricShard017Summary token).range.run.positionTrace =
      PositionTrace.consecutive 136 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
