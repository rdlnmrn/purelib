import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk046

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard046_positionTrace (token : Unit) :
    (geometricShard046Summary token).range.run.positionTrace =
      PositionTrace.consecutive 736 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
