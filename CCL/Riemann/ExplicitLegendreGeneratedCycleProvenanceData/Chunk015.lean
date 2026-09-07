import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk015

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard015_positionTrace (token : Unit) :
    (geometricShard015Summary token).range.run.positionTrace =
      PositionTrace.consecutive 240 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
