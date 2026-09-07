import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk073

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard073_positionTrace (token : Unit) :
    (geometricShard073Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1168 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
