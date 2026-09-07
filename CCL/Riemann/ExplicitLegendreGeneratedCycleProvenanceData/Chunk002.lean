import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk002

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard002_positionTrace (token : Unit) :
    (geometricShard002Summary token).range.run.positionTrace =
      PositionTrace.consecutive 32 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
