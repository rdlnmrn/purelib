import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk057

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard057_positionTrace (token : Unit) :
    (geometricShard057Summary token).range.run.positionTrace =
      PositionTrace.consecutive 912 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
