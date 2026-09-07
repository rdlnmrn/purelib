import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk109

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard109_positionTrace (token : Unit) :
    (geometricShard109Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1744 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
