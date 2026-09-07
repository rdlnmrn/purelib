import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk235

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard235_positionTrace (token : Unit) :
    (geometricShard235Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3760 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
