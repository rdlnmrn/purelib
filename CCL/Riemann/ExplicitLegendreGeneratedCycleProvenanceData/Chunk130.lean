import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk130

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard130_positionTrace (token : Unit) :
    (geometricShard130Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2080 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
