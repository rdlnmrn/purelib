import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk015

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard015_positionTrace (token : Unit) :
    (geometricShard015Summary token).range.run.positionTrace =
      PositionTrace.consecutive 120 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
