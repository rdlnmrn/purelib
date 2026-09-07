import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk018

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard018_positionTrace (token : Unit) :
    (geometricShard018Summary token).range.run.positionTrace =
      PositionTrace.consecutive 288 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
