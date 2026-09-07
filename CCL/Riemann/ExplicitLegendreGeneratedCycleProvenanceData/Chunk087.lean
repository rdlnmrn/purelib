import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk087

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard087_positionTrace (token : Unit) :
    (geometricShard087Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1392 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
