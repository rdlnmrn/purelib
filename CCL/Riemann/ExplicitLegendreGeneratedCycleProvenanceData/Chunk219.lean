import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk219

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard219_positionTrace (token : Unit) :
    (geometricShard219Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3504 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
