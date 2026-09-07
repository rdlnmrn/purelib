import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk190

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard190_positionTrace (token : Unit) :
    (geometricShard190Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3040 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
