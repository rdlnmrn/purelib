import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk020

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard020_positionTrace (token : Unit) :
    (geometricShard020Summary token).range.run.positionTrace =
      PositionTrace.consecutive 320 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
