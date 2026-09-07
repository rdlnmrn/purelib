import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk004

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard004_positionTrace (token : Unit) :
    (geometricShard004Summary token).range.run.positionTrace =
      PositionTrace.consecutive 64 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
