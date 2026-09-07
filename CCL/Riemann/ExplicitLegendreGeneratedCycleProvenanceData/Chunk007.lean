import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk007

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard007_positionTrace (token : Unit) :
    (geometricShard007Summary token).range.run.positionTrace =
      PositionTrace.consecutive 112 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
