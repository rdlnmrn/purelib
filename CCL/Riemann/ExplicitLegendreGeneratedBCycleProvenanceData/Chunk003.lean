import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk003

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard003_positionTrace (token : Unit) :
    (geometricShard003Summary token).range.run.positionTrace =
      PositionTrace.consecutive 24 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
