import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk040

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard040_positionTrace (token : Unit) :
    (geometricShard040Summary token).range.run.positionTrace =
      PositionTrace.consecutive 640 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
