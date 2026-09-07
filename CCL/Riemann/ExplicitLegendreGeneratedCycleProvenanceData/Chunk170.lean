import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk170

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard170_positionTrace (token : Unit) :
    (geometricShard170Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2720 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
