import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk206

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard206_positionTrace (token : Unit) :
    (geometricShard206Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3296 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
