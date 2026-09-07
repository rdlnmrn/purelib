import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk009

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard009_positionTrace (token : Unit) :
    (geometricShard009Summary token).range.run.positionTrace =
      PositionTrace.consecutive 72 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
