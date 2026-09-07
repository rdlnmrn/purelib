import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk160

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard160_positionTrace (token : Unit) :
    (geometricShard160Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2560 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
