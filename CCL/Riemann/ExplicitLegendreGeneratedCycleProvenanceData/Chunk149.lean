import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk149

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard149_positionTrace (token : Unit) :
    (geometricShard149Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2384 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
