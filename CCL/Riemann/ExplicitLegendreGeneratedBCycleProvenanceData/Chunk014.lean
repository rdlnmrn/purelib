import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk014

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard014_positionTrace (token : Unit) :
    (geometricShard014Summary token).range.run.positionTrace =
      PositionTrace.consecutive 112 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
