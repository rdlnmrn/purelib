import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk118

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard118_positionTrace (token : Unit) :
    (geometricShard118Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1888 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
