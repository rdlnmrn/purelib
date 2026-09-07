import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk031

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard031_positionTrace (token : Unit) :
    (geometricShard031Summary token).range.run.positionTrace =
      PositionTrace.consecutive 496 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
