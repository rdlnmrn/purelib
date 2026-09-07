import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk189

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard189_positionTrace (token : Unit) :
    (geometricShard189Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3024 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
