import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk191

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard191_positionTrace (token : Unit) :
    (geometricShard191Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3056 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
