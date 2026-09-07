import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk220

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard220_positionTrace (token : Unit) :
    (geometricShard220Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3520 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
