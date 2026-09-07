import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk192

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard192_positionTrace (token : Unit) :
    (geometricShard192Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3072 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
