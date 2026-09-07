import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk027

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard027_positionTrace (token : Unit) :
    (geometricShard027Summary token).range.run.positionTrace =
      PositionTrace.consecutive 432 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
