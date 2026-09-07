import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk072

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard072_positionTrace (token : Unit) :
    (geometricShard072Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1152 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
