import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk195

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard195_positionTrace (token : Unit) :
    (geometricShard195Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3120 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
