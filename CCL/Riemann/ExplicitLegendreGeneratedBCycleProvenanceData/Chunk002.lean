import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk002

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard002_positionTrace (token : Unit) :
    (geometricShard002Summary token).range.run.positionTrace =
      PositionTrace.consecutive 16 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
