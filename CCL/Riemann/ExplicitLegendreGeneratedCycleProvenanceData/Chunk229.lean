import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk229

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard229_positionTrace (token : Unit) :
    (geometricShard229Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3664 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
