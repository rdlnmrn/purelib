import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk028

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard028_positionTrace (token : Unit) :
    (geometricShard028Summary token).range.run.positionTrace =
      PositionTrace.consecutive 448 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
