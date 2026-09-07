import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk032

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard032_positionTrace (token : Unit) :
    (geometricShard032Summary token).range.run.positionTrace =
      PositionTrace.consecutive 512 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
