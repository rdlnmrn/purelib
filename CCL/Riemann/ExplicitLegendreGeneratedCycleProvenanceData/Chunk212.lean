import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk212

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard212_positionTrace (token : Unit) :
    (geometricShard212Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3392 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
