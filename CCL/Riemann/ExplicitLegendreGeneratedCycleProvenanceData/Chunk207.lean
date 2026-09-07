import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk207

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard207_positionTrace (token : Unit) :
    (geometricShard207Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3312 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
