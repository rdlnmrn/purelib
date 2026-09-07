import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk019

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard019_positionTrace (token : Unit) :
    (geometricShard019Summary token).range.run.positionTrace =
      PositionTrace.consecutive 304 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
