import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk086

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard086_positionTrace (token : Unit) :
    (geometricShard086Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1376 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
