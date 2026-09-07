import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk091

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard091_positionTrace (token : Unit) :
    (geometricShard091Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1456 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
