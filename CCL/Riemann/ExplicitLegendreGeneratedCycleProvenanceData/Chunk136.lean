import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk136

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard136_positionTrace (token : Unit) :
    (geometricShard136Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2176 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
