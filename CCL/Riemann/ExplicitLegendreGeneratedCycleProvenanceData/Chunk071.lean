import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk071

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard071_positionTrace (token : Unit) :
    (geometricShard071Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1136 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
