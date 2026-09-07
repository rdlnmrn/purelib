import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk038

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard038_positionTrace (token : Unit) :
    (geometricShard038Summary token).range.run.positionTrace =
      PositionTrace.consecutive 608 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
