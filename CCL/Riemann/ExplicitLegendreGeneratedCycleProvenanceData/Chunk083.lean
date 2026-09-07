import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk083

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard083_positionTrace (token : Unit) :
    (geometricShard083Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1328 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
