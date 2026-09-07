import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk020

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard020_positionTrace (token : Unit) :
    (geometricShard020Summary token).range.run.positionTrace =
      PositionTrace.consecutive 160 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
