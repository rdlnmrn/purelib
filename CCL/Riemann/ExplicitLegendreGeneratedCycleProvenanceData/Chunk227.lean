import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk227

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard227_positionTrace (token : Unit) :
    (geometricShard227Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3632 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
