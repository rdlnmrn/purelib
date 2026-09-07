import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk029

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard029_positionTrace (token : Unit) :
    (geometricShard029Summary token).range.run.positionTrace =
      PositionTrace.consecutive 232 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
