import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk186

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard186_positionTrace (token : Unit) :
    (geometricShard186Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2976 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
