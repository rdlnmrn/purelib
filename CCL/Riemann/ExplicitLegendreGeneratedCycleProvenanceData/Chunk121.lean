import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk121

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard121_positionTrace (token : Unit) :
    (geometricShard121Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1936 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
