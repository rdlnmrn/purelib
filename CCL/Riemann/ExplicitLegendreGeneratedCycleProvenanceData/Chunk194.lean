import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk194

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard194_positionTrace (token : Unit) :
    (geometricShard194Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3104 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
