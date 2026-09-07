import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk123

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard123_positionTrace (token : Unit) :
    (geometricShard123Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1968 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
