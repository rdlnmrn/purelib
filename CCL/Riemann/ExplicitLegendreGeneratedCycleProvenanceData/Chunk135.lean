import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk135

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard135_positionTrace (token : Unit) :
    (geometricShard135Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2160 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
