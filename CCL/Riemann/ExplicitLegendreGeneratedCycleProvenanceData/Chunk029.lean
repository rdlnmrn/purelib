import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk029

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard029_positionTrace (token : Unit) :
    (geometricShard029Summary token).range.run.positionTrace =
      PositionTrace.consecutive 464 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
