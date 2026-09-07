import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk234

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard234_positionTrace (token : Unit) :
    (geometricShard234Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3744 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
