import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk144

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard144_positionTrace (token : Unit) :
    (geometricShard144Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2304 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
