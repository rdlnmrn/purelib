import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk177

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard177_positionTrace (token : Unit) :
    (geometricShard177Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2832 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
