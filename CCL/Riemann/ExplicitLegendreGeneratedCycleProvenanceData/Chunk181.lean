import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk181

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard181_positionTrace (token : Unit) :
    (geometricShard181Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2896 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
