import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk116

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard116_positionTrace (token : Unit) :
    (geometricShard116Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1856 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
