import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk203

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard203_positionTrace (token : Unit) :
    (geometricShard203Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3248 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
