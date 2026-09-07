import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk032

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard032_positionTrace (token : Unit) :
    (geometricShard032Summary token).range.run.positionTrace =
      PositionTrace.consecutive 256 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
