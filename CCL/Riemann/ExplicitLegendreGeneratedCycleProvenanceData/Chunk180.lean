import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk180

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard180_positionTrace (token : Unit) :
    (geometricShard180Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2880 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
