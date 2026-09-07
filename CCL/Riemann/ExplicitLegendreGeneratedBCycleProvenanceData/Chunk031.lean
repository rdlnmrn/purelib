import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk031

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard031_positionTrace (token : Unit) :
    (geometricShard031Summary token).range.run.positionTrace =
      PositionTrace.consecutive 248 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
