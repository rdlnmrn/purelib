import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk216

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard216_positionTrace (token : Unit) :
    (geometricShard216Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3456 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
