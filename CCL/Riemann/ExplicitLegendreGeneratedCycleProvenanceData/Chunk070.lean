import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk070

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard070_positionTrace (token : Unit) :
    (geometricShard070Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1120 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
