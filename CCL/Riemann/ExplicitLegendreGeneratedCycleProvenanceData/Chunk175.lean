import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk175

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard175_positionTrace (token : Unit) :
    (geometricShard175Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2800 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
