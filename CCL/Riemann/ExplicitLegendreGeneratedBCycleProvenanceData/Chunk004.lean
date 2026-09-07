import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk004

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard004_positionTrace (token : Unit) :
    (geometricShard004Summary token).range.run.positionTrace =
      PositionTrace.consecutive 32 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
