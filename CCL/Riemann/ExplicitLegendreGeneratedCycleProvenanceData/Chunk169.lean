import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk169

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard169_positionTrace (token : Unit) :
    (geometricShard169Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2704 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
