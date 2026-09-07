import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk003

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard003_positionTrace (token : Unit) :
    (geometricShard003Summary token).range.run.positionTrace =
      PositionTrace.consecutive 48 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
