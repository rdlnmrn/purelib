import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk224

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard224_positionTrace (token : Unit) :
    (geometricShard224Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3584 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
