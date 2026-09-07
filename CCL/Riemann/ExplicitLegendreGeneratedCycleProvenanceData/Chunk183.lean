import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk183

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard183_positionTrace (token : Unit) :
    (geometricShard183Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2928 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
