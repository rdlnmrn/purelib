import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk127

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard127_positionTrace (token : Unit) :
    (geometricShard127Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2032 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
