import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk174

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard174_positionTrace (token : Unit) :
    (geometricShard174Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2784 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
