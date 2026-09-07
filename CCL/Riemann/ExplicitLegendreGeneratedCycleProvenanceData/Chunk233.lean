import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk233

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard233_positionTrace (token : Unit) :
    (geometricShard233Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3728 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
