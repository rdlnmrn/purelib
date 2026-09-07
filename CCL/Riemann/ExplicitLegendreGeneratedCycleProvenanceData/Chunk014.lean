import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk014

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard014_positionTrace (token : Unit) :
    (geometricShard014Summary token).range.run.positionTrace =
      PositionTrace.consecutive 224 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
