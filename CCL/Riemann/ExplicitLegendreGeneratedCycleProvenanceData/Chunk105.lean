import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk105

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard105_positionTrace (token : Unit) :
    (geometricShard105Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1680 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
