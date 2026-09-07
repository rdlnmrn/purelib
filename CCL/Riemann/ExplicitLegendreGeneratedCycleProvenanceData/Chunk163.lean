import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk163

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard163_positionTrace (token : Unit) :
    (geometricShard163Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2608 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
