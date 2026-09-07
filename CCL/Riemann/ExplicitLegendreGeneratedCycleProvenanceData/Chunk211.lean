import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk211

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard211_positionTrace (token : Unit) :
    (geometricShard211Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3376 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
