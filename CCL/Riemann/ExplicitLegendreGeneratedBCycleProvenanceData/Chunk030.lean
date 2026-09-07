import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk030

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard030_positionTrace (token : Unit) :
    (geometricShard030Summary token).range.run.positionTrace =
      PositionTrace.consecutive 240 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
