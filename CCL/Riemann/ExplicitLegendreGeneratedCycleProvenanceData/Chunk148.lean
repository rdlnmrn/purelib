import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk148

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard148_positionTrace (token : Unit) :
    (geometricShard148Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2368 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
