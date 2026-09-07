import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk030

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard030_positionTrace (token : Unit) :
    (geometricShard030Summary token).range.run.positionTrace =
      PositionTrace.consecutive 480 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
