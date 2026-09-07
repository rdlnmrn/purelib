import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk165

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard165_positionTrace (token : Unit) :
    (geometricShard165Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2640 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
