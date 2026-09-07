import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk033

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard033_positionTrace (token : Unit) :
    (geometricShard033Summary token).range.run.positionTrace =
      PositionTrace.consecutive 264 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
