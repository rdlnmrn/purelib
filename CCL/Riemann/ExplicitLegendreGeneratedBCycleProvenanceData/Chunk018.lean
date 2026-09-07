import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk018

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard018_positionTrace (token : Unit) :
    (geometricShard018Summary token).range.run.positionTrace =
      PositionTrace.consecutive 144 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
