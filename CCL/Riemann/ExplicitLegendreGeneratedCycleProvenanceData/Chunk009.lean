import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk009

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard009_positionTrace (token : Unit) :
    (geometricShard009Summary token).range.run.positionTrace =
      PositionTrace.consecutive 144 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
