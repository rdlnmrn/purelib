import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk089

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard089_positionTrace (token : Unit) :
    (geometricShard089Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1424 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
