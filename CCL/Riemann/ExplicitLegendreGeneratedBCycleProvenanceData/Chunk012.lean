import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk012

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard012_positionTrace (token : Unit) :
    (geometricShard012Summary token).range.run.positionTrace =
      PositionTrace.consecutive 96 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
