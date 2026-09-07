import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk230

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard230_positionTrace (token : Unit) :
    (geometricShard230Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3680 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
