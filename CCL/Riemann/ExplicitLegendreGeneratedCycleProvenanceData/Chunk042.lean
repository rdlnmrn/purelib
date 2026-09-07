import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk042

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard042_positionTrace (token : Unit) :
    (geometricShard042Summary token).range.run.positionTrace =
      PositionTrace.consecutive 672 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
