import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk222

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard222_positionTrace (token : Unit) :
    (geometricShard222Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3552 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
