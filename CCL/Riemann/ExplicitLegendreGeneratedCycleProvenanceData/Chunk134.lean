import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk134

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard134_positionTrace (token : Unit) :
    (geometricShard134Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2144 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
