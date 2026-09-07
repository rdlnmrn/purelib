import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk054

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard054_positionTrace (token : Unit) :
    (geometricShard054Summary token).range.run.positionTrace =
      PositionTrace.consecutive 864 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
