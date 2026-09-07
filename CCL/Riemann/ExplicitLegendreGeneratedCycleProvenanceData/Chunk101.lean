import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk101

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard101_positionTrace (token : Unit) :
    (geometricShard101Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1616 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
