import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk052

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard052_positionTrace (token : Unit) :
    (geometricShard052Summary token).range.run.positionTrace =
      PositionTrace.consecutive 832 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
