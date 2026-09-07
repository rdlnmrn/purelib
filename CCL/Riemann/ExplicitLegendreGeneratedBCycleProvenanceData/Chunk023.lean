import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk023

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard023_positionTrace (token : Unit) :
    (geometricShard023Summary token).range.run.positionTrace =
      PositionTrace.consecutive 184 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
