import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk019

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard019_positionTrace (token : Unit) :
    (geometricShard019Summary token).range.run.positionTrace =
      PositionTrace.consecutive 152 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
