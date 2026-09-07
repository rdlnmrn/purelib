import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk164

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard164_positionTrace (token : Unit) :
    (geometricShard164Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2624 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
