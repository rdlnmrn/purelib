import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk238

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard238_positionTrace (token : Unit) :
    (geometricShard238Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3808 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
